// Copyright 2022 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

// Author: Robert Balas <balasr@iis.ee.ethz.ch>

module cv32e40p_shadow_controller #(
  parameter int unsigned ADDR_WIDTH = 6,
  parameter int unsigned DATA_WIDTH = 32,
  parameter int unsigned NUM_SHADOW_SAVES = 7
) (
  input logic                   clk_i,
  input logic                   rst_ni,
  input logic                   setback_i,
  // from/to core controller indicating an interrupt
  input logic                   shadow_irq_i,
  // whether we are ready to process another interrupt (for nesting)
  output logic                  shadow_ready_o,
  output logic [ADDR_WIDTH-1:0] shadow_save_level_o,
  // from/to shadow register
  output logic [ADDR_WIDTH-1:0] shadow_reg_raddr_o,
  input logic [DATA_WIDTH-1:0]  shadow_reg_rdata_i,
  input logic [DATA_WIDTH-1:0]  shadow_reg_sp_i,
  // from/to memory
  output logic                  shadow_req_o,
  input logic                   shadow_gnt_i,
  input logic                   shadow_rvalid_i,
  output logic                  shadow_we_o,
  output logic [3:0]            shadow_be_o,
  output logic [31:0]           shadow_addr_o,
  output logic [31:0]           shadow_wdata_o,
  input logic [31:0]            shadow_rdata_i // unconnected, we don't read
);

  logic [ADDR_WIDTH-1:0] cnt_q, cnt_d;
  logic [31:0]           stack_q, stack_d;

  localparam int unsigned SHADOW_RELOAD = NUM_SHADOW_SAVES - 1;

  typedef enum logic [1:0] {
    IDLE, SAVE
  } save_state_e;

  save_state_e save_state_d, save_state_q;

  always_comb begin
    save_state_d = save_state_q;
    cnt_d = cnt_q;
    stack_d = stack_q;

    shadow_req_o = 1'b0;
    shadow_we_o = 1'b0;
    shadow_be_o = 4'b0000;
    shadow_addr_o = 32'b0;
    shadow_wdata_o = 32'b0;

    shadow_ready_o = 1'b0;

    unique case (save_state_q)
      IDLE: begin
        cnt_d = SHADOW_RELOAD;
        shadow_ready_o = 1'b1;
        if (shadow_irq_i) begin
          save_state_d = SAVE;
          // the stack register points to the last already used address
          stack_d      = shadow_reg_sp_i - 4;
        end
      end

      SAVE: begin
        // write reg to stack
        shadow_req_o = 1'b1;
        shadow_we_o = 1'b1;
        shadow_be_o = 4'b1111;
        shadow_addr_o = stack_q;
        shadow_wdata_o = shadow_reg_rdata_i;

        shadow_ready_o = 1'b0;

        // the shadow register now contain the interrupt context
        if (shadow_req_o && shadow_gnt_i) begin
          if (cnt_q == 0) begin
            save_state_d = IDLE;
            cnt_d        = SHADOW_RELOAD;
            stack_d      = 32'b0;
          end else begin
            cnt_d = cnt_q - 1;
            stack_d = stack_q - 4;
          end
        end
      end

      default:;
    endcase // unique case (save_state_q)
  end

  assign shadow_save_level_o = cnt_q;
  assign shadow_reg_raddr_o = cnt_q;

  always_ff @(posedge clk_i or negedge rst_ni) begin
    if (!rst_ni) begin
      save_state_q <= IDLE;
      stack_q      <= '0;
      cnt_q        <= SHADOW_RELOAD;
    end else begin
      if (setback_i) begin
        save_state_q <= IDLE;
        stack_q      <= '0;
        cnt_q        <= SHADOW_RELOAD;
      end else begin
        save_state_q <= save_state_d;
        stack_q      <= stack_d;
        cnt_q        <= cnt_d;
      end
    end
  end

    // TODO: Use CV32E40P_ASSERT_ON
`ifndef SYNTHESIS
`ifndef VERILATOR
  a_shadow_controller_acces_while_saving: assert property (
    @(posedge clk_i) disable iff (!rst_ni)
    save_state_q == SAVE |-> !shadow_irq_i)
    else
      $error("shadow register access is out of range");
`endif
`endif


endmodule
