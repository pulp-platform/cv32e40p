// Copyright 2018 ETH Zurich and University of Bologna.
// Copyright and related rights are licensed under the Solderpad Hardware
// License, Version 0.51 (the "License"); you may not use this file except in
// compliance with the License.  You may obtain a copy of the License at
// http://solderpad.org/licenses/SHL-0.51. Unless required by applicable law
// or agreed to in writing, software, hardware and materials distributed under
// this License is distributed on an "AS IS" BASIS, WITHOUT WARRANTIES OR
// CONDITIONS OF ANY KIND, either express or implied. See the License for the
// specific language governing permissions and limitations under the License.

////////////////////////////////////////////////////////////////////////////////
// Engineer:       Francesco Conti - f.conti@unibo.it                         //
//                                                                            //
// Additional contributions by:                                               //
//                 Michael Gautschi - gautschi@iis.ee.ethz.ch                 //
//                 Davide Schiavone - pschiavo@iis.ee.ethz.ch                 //
//                                                                            //
// Design Name:    RISC-V register file                                       //
// Project Name:   RI5CY                                                      //
// Language:       SystemVerilog                                              //
//                                                                            //
// Description:    Register file with 31x 32 bit wide registers. Register 0   //
//                 is fixed to 0. This register file is based on flip-flops.  //
//                 Also supports the fp-register file now if FPU=1            //
//                 If PULP_ZFINX is 1, floating point operations take values  //
//                 from the X register file                                   //
//                                                                            //
////////////////////////////////////////////////////////////////////////////////

module cv32e40p_register_file
#(
    parameter ADDR_WIDTH     = 5,
    parameter DATA_WIDTH     = 32,
    parameter FPU            = 0,
    parameter PULP_ZFINX     = 0,
    parameter NUM_INTERRUPTS = 32,
    parameter SHADOW         = 0,
    parameter ABI            = "standard"
)
(
    // Clock and Reset
    input  logic         clk,
    input  logic         rst_n,

    input  logic         scan_cg_en_i,

    //Read port R1
    input  logic [ADDR_WIDTH-1:0]  raddr_a_i,
    output logic [DATA_WIDTH-1:0]  rdata_a_o,

    //Read port R2
    input  logic [ADDR_WIDTH-1:0]  raddr_b_i,
    output logic [DATA_WIDTH-1:0]  rdata_b_o,

    //Read port R3
    input  logic [ADDR_WIDTH-1:0]  raddr_c_i,
    output logic [DATA_WIDTH-1:0]  rdata_c_o,

    // Write port W1
    input logic [ADDR_WIDTH-1:0]   waddr_a_i,
    input logic [DATA_WIDTH-1:0]   wdata_a_i,
    input logic                    we_a_i,

    // Write port W2
    input logic [ADDR_WIDTH-1:0]   waddr_b_i,
    input logic [DATA_WIDTH-1:0]   wdata_b_i,
    input logic                    we_b_i,

    // shadow csr registers
    input logic                            shadow_csr_save_i,
    input logic [31:0]                     shadow_mepc_i,
    input logic [$clog2(NUM_INTERRUPTS):0] shadow_mcause_i,

    // shadow csr registers
    input logic                    shadow_save_i,

    // shadow registers - read port
    input  logic [ADDR_WIDTH-1:0]  shadow_raddr_i,
    output logic [DATA_WIDTH-1:0]  shadow_rdata_o,
    output logic [DATA_WIDTH-1:0]  shadow_sp_o
);

  // number of integer registers
  localparam    NUM_WORDS        = 2**(ADDR_WIDTH-1);
  localparam    NUM_WORDS_SHADOW = ABI == "standard" ? 16 : (ABI == "eabi" ? 7 : -1);

  // number of floating point registers
  localparam    NUM_FP_WORDS  = 2**(ADDR_WIDTH-1);
  localparam    NUM_TOT_WORDS = FPU ? ( PULP_ZFINX ? NUM_WORDS : NUM_WORDS + NUM_FP_WORDS ) : NUM_WORDS;

  // integer register file
  logic [NUM_WORDS-1:0][DATA_WIDTH-1:0]     mem;

  // shadow integer register file
  logic [NUM_WORDS_SHADOW-1:0][DATA_WIDTH-1:0] mem_shadow;

  // shadow csrs
  logic [31:0]                                 shadow_mepc;
  logic [$clog2(NUM_INTERRUPTS):0]             shadow_mcause;

  // fp register file
  logic [NUM_FP_WORDS-1:0][DATA_WIDTH-1:0]  mem_fp;

  // masked write addresses
  logic [ADDR_WIDTH-1:0]                    waddr_a;
  logic [ADDR_WIDTH-1:0]                    waddr_b;

  // write enable signals for all registers
  logic [NUM_TOT_WORDS-1:0]                 we_a_dec;
  logic [NUM_TOT_WORDS-1:0]                 we_b_dec;


  //-----------------------------------------------------------------------------
  //-- READ : Read address decoder RAD
  //-----------------------------------------------------------------------------
  generate
    if (FPU == 1 && PULP_ZFINX == 0) begin : gen_mem_fp_read
       assign rdata_a_o = raddr_a_i[5] ? mem_fp[raddr_a_i[4:0]] : mem[raddr_a_i[4:0]];
       assign rdata_b_o = raddr_b_i[5] ? mem_fp[raddr_b_i[4:0]] : mem[raddr_b_i[4:0]];
       assign rdata_c_o = raddr_c_i[5] ? mem_fp[raddr_c_i[4:0]] : mem[raddr_c_i[4:0]];
    end else begin : gen_mem_read
       assign rdata_a_o = mem[raddr_a_i[4:0]];
       assign rdata_b_o = mem[raddr_b_i[4:0]];
       assign rdata_c_o = mem[raddr_c_i[4:0]];
    end
  endgenerate

  //-----------------------------------------------------------------------------
  //-- WRITE : Write Address Decoder (WAD), combinatorial process
  //-----------------------------------------------------------------------------

  // Mask top bit of write address to disable fp regfile
  assign waddr_a = waddr_a_i;
  assign waddr_b = waddr_b_i;

  genvar gidx;
  generate
    for (gidx=0; gidx<NUM_TOT_WORDS; gidx++) begin : gen_we_decoder
      assign we_a_dec[gidx] = (waddr_a == gidx) ? we_a_i : 1'b0;
      assign we_b_dec[gidx] = (waddr_b == gidx) ? we_b_i : 1'b0;
    end
  endgenerate

  genvar i,l;
  generate

    //-----------------------------------------------------------------------------
    //-- WRITE : Write operation
    //-----------------------------------------------------------------------------
    // R0 is nil
    always_ff @(posedge clk or negedge rst_n) begin
      if(~rst_n) begin
        // R0 is nil
        mem[0] <= 32'b0;
      end else begin
        // R0 is nil
        mem[0] <= 32'b0;
      end
    end

    // loop from 1 to NUM_WORDS-1 as R0 is nil
    for (i = 1; i < NUM_WORDS; i++)
    begin : gen_rf

      always_ff @(posedge clk, negedge rst_n)
      begin : register_write_behavioral
        if (rst_n==1'b0) begin
          mem[i] <= 32'b0;
        end else begin
          if (i == 2 && shadow_save_i) begin
            // shadow register save bumps the stack pointer too
            // TODO: if a write happens to sp at the same time as a
            // shadow_save_i request, we might lose the write..
            mem[i] <= mem[i] - NUM_WORDS_SHADOW * 4;
          end else if(we_b_dec[i] == 1'b1)
            mem[i] <= wdata_b_i;
          else if(we_a_dec[i] == 1'b1)
            mem[i] <= wdata_a_i;
        end
      end

    end

    if (FPU == 1 && PULP_ZFINX == 0) begin : gen_mem_fp_write
      // Floating point registers
      for(l = 0; l < NUM_FP_WORDS; l++) begin
        always_ff @(posedge clk, negedge rst_n)
        begin : fp_regs
          if (rst_n==1'b0)
            mem_fp[l] <= '0;
          else if(we_b_dec[l+NUM_WORDS] == 1'b1)
            mem_fp[l] <= wdata_b_i;
          else if(we_a_dec[l+NUM_WORDS] == 1'b1)
            mem_fp[l] <= wdata_a_i;
        end
      end
    end else begin : gen_no_mem_fp_write
      assign mem_fp = 'b0;
    end

  endgenerate

  // TODO: order according to https://www.ocf.berkeley.edu/~qmn/linux/riscv.html to improve exceptions?
  // save to shadow register
  // ABI (integer) has the following caller-save registers (16)
  // ra x1
  // t0 x5
  // t1 x6
  // t2 x7
  // a0 x10
  // a1 x11
  // a2 x12
  // a3 x13
  // a4 x14
  // a5 x15
  // a6 x16
  // a7 x17
  // t3 x28
  // t4 x29
  // t5 x30
  // t6 x31

  // EABI has the following caller-save registers (7)
  // ra x1
  // t0 x5
  // a0 x10
  // a1 x11
  // a2 x12
  // a3 x13
  // t1 x15
  // (optional) sp (x2) needs to point to new interrupt stack
  // (optional) gp (x3) needs to point to new small data section
  // (optional) tp (x4) needs to point to different thread-local storage region


if (SHADOW) begin: gen_shadow_save
  if (NUM_WORDS_SHADOW != 7 && NUM_WORDS_SHADOW != 16)
    $fatal(1, "NUM_WORDS_SHADOW needs to be 7 or 16 (EABI or standard)");

  if (ABI == "standard" && ((NUM_WORDS_SHADOW * 4) % 16) != 0)
    $fatal(1, "stack increment needs to be 16-byte aligned for standard ABI");

  always_ff @(posedge clk or negedge rst_n) begin
      if(~rst_n) begin
        mem_shadow <= '0;
      end else begin
        if (shadow_save_i) begin
          if (ABI == "standard") begin : gen_reg_standard
            // save standard caller save registers
            mem_shadow[0] <= mem[1];
            mem_shadow[1] <= mem[5];
            mem_shadow[2] <= mem[6];
            mem_shadow[3] <= mem[7];
            mem_shadow[4] <= mem[10];
            mem_shadow[5] <= mem[11];
            mem_shadow[6] <= mem[12];
            mem_shadow[7] <= mem[13];
            mem_shadow[8] <= mem[14];
            mem_shadow[9] <= mem[15];
            mem_shadow[10] <= mem[16];
            mem_shadow[11] <= mem[17];
            mem_shadow[12] <= mem[28];
            mem_shadow[13] <= mem[29];
            mem_shadow[14] <= mem[30];
            mem_shadow[15] <= mem[31];
          end else if (ABI == "eabi") begin : gen_reg_eabi
            // save eabi caller save registers
            mem_shadow[0] <= mem[1];
            mem_shadow[1] <= mem[5];
            mem_shadow[2] <= mem[10];
            mem_shadow[3] <= mem[11];
            mem_shadow[4] <= mem[12];
            mem_shadow[5] <= mem[13];
            mem_shadow[6] <= mem[15];
          end
        end
      end
  end

  always_ff @(posedge clk or negedge rst_n) begin
    if (~rst_n) begin
      shadow_mepc   <= '0;
      shadow_mcause <= '0;
    end else begin
      if (shadow_csr_save_i) begin
        shadow_mepc   <= shadow_mepc_i;
        shadow_mcause <= shadow_mcause_i;
      end
    end
  end

  assign shadow_rdata_o = mem_shadow[shadow_raddr_i];
  assign shadow_sp_o    = mem[2];

  // TODO: Use CV32E40P_ASSERT_ON
`ifndef SYNTHESIS
`ifndef VERILATOR
  a_shadow_acces_in_range: assert property (
    @(posedge clk) disable iff (!rst_n)
    shadow_save_i |-> shadow_raddr_i < NUM_WORDS_SHADOW)
    else
      $error("shadow register access is out of range");

  a_shadow_bump_sp_collision: assert property (
    @(posedge clk) disable iff (!rst_n)
    shadow_save_i |-> we_b_dec[2] != 1'b1 && we_a_dec[2] != 1'b1)
    else
      $fatal(1, "shadow register write collision on stack pointer reg");
`endif
`endif

end else begin : gen_no_shadow_save
  assign shadow_mepc = '0;
  assign shadow_mcause = '0;
  assign shadow_rdata_o = '0;
  assign shadow_sp_o = '0;
  assign mem_shadow = '0;
end

endmodule
