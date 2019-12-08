`timescale 1ns/1ps
`define mydelay 1

//--------------------------------------------------------------
// mips.v
// David_Harris@hmc.edu and Sarah_Harris@hmc.edu 23 October 2005
// Single-cycle MIPS processor
//--------------------------------------------------------------

// single-cycle MIPS processor
module mips(input         clk, reset,
            output [31:0] pc,
            input  [31:0] instr,
            output        memwrite,
            output [31:0] memaddr,
            output [31:0] memwritedata,
            input  [31:0] memreaddata);
				
  wire        signext_h, shiftl16_e, memtoreg_w, memtoreg_e;
  wire        pcsrc, zero, hazardcon, branch_e, branchne_e;
  wire        alusrc_ex, regdst_e, regwrite_w, regwrite_m, jump_e, jal_e;
  wire [2:0]  alucontrol;
  wire [31:0] instr_d;
 
  // Instantiate Controller
  controller c(
      .op           (instr_d[31:26]), 
		.funct        (instr_d[5:0]), 
		.clk          (clk),
		.reset        (reset),
		.zero         (zero),
		.signext_h    (signext_h),
		.shiftl16_e	  (shiftl16_e),
		.memtoreg_e   (memtoreg_e),
		.memtoreg_w   (memtoreg_w),
		.memwrite     (memwrite),
		.pcsrc        (pcsrc),
		.branch_e     (branch_e),
		.branchne_e   (branchne_e),
		.alusrc_ex    (alusrc_ex),
		.regdst_e     (regdst_e),
		.regwrite_w   (regwrite_w),
		.regwrite_m   (regwrite_m),
		.jump_e       (jump_e),
		.jal_e        (jal_e),
		.hazardcon    (hazardcon),
		.alucontrol   (alucontrol));

  // Instantiate Datapath
  datapath dp(
    .clk          (clk),
    .reset        (reset),
	 .instr			(instr),
	 .instr_d      (instr_d),
    .signext_h    (signext_h),
    .shiftl16_e   (shiftl16_e),
    .memtoreg_w   (memtoreg_w),
    .pcsrc        (pcsrc),
	 .branch_e     (branch_e),
	 .branchne_e   (branchne_e),
    .alusrc_ex    (alusrc_ex),
    .regdst_e     (regdst_e),
    .regwrite_w   (regwrite_w),
	 .regwrite_m   (regwrite_m),
	 .memtoreg_e   (memtoreg_e),
    .jump_e       (jump_e),
	 .jal_e        (jal_e),
	 .hazardcon    (hazardcon),
    .alucontrol   (alucontrol),
    .zero         (zero),
	 .pc           (pc),
    .aluout_m     (memaddr), 
    .writedata_m  (memwritedata),
    .readdata     (memreaddata));
	 
endmodule

module controller(input        clk, reset,
                  input  [5:0] op, funct,
                  input        zero,
						input        hazardcon,
                  output       signext_h,
                  output       shiftl16_e, memtoreg_e,
                  output       memtoreg_w, regwrite_w, regwrite_m,
                  output       pcsrc, jump_e,
                  output       memwrite, 
                  output       alusrc_ex, regdst_e,
						output       jal_e,
						output       branch_e, branchne_e,
                  output [2:0] alucontrol);

  wire       branch_h, branchne_h, memwrite_e;
  wire       memtoreg_m, shiftl16, shiftl16_h;
  wire       branchne, memtoreg, memwrite_m, branch, alusrc, regdst, regwrite, regwrite_e;
  wire       signext, regwrite_h, regdst_h, alusrc_h, memwrite_h, memtoreg_h, jump, jal;
  wire [1:0] aluop, aluop_e, aluop_h;
  wire [5:0] funct_ex;
  
  maindec md(
    .op         (op),
    .signext    (signext),
    .shiftl16   (shiftl16),
    .memtoreg   (memtoreg),
    .memwrite_m (memwrite_m),
    .branch     (branch),
	 .branchne   (branchne),
    .alusrc     (alusrc),
    .regdst     (regdst),
    .regwrite   (regwrite),
    .jump       (jump),
	 .jal        (jal),
    .aluop      (aluop));

  aludec ad( 
    .funct      (funct_ex), 
    .aluop_e    (aluop_e), 
    .alucontrol (alucontrol));
	 
  IDEX_CON IC(                            // memtoreg & regwrite & branch & memwrite & regdst & aluop & alusrc after ID/EX
    .clk               (clk), 
    .reset             (reset),
	 .memtoreg_e        (memtoreg_e),
	 .memtoreg_h        (memtoreg_h),
	 .regwrite_e        (regwrite_e),
	 .regwrite_h        (regwrite_h),
	 .branch_e          (branch_e),
	 .branch_h          (branch_h),
	 .branchne_e        (branchne_e),
	 .branchne_h        (branchne_h),
	 .jump_e            (jump_e),
	 .jump_h            (jump_h),
	 .jal_e             (jal_e),
	 .jal_h             (jal_h),
	 .shiftl16_e        (shiftl16_e),
	 .shiftl16_h        (shiftl16_h),
	 .memwrite_e        (memwrite_e),
	 .memwrite_h        (memwrite_h),
	 .funct_id          (funct),
	 .funct_ex          (funct_ex),
	 .regdst_h          (regdst_h),
	 .aluop_h           (aluop_h),
	 .alusrc_h          (alusrc_h),
	 .regdst_e          (regdst_e),
	 .aluop_e           (aluop_e),
	 .alusrc_ex         (alusrc_ex));
	 
	 EXMEM_CON EC(                          // memtoreg & regwrite & branch & memwrite after EX/MEM
    .clk               (clk), 
    .reset             (reset),
	 .memtoreg_e        (memtoreg_e),
	 .memtoreg_m        (memtoreg_m),
	 .regwrite_e        (regwrite_e),
	 .regwrite_m        (regwrite_m),
	 .memwrite_e        (memwrite_e),
	 .memwrite          (memwrite));
	 
	 MEMWB_CON MC(                          // memtoreg & regwrite after MEM/WB
    .clk               (clk), 
    .reset             (reset),
	 .memtoreg_w        (memtoreg_w),
	 .memtoreg_m        (memtoreg_m),
	 .regwrite_w        (regwrite_w),
	 .regwrite_m        (regwrite_m));
	 
	 mux2 #(13) hazardmux(
    .d0   ({signext, shiftl16, regwrite, regdst, alusrc, branch, branchne, memwrite_m, memtoreg, jump, jal, aluop}),
    .d1   (13'b0),
    .s    (hazardcon),
    .y    ({signext_h, shiftl16_h, regwrite_h, regdst_h, alusrc_h, branch_h, branchne_h, memwrite_h, memtoreg_h, jump_h, jal_h, aluop_h}));
			 
  assign pcsrc = (branch_e&zero) | (branchne_e&~zero); 
endmodule

module IDEX_CON(input              clk, reset,    // memtoreg & regwrite & branch & memwrite & regdst & aluop & alusrc & jump & jal after ID/EX
                input              regdst_h, branch_h, memwrite_h, branchne_h, jump_h, jal_h, shiftl16_h,
					 input      [1:0]   aluop_h,
					 input      [5:0]   funct_id,
					 input       		  alusrc_h,	memtoreg_h, regwrite_h,					 
					 output reg   	     regdst_e, branch_e, memwrite_e, memtoreg_e, regwrite_e, branchne_e, jump_e, jal_e, shiftl16_e,
					 output reg [1:0]   aluop_e,
					 output reg [5:0]   funct_ex,
					 output reg         alusrc_ex);
	  always @(posedge clk or posedge reset)  
    begin
         if (reset) 
            begin
               regdst_e   <= #`mydelay 1'b0;
					aluop_e    <= #`mydelay 2'b0;
					alusrc_ex  <= #`mydelay 1'b0;
					funct_ex   <= #`mydelay 6'b0;
					branch_e   <= #`mydelay 1'b0;
					branchne_e <= #`mydelay 1'b0;
					memwrite_e <= #`mydelay 1'b0;
					memtoreg_e <= #`mydelay 1'b0;
					regwrite_e <= #`mydelay 1'b0;
					jump_e     <= #`mydelay 1'b0;
					jal_e      <= #`mydelay 1'b0;
					shiftl16_e <= #`mydelay 1'b0;
            end
         else
            begin
               regdst_e   <= #`mydelay regdst_h;
					aluop_e    <= #`mydelay aluop_h;
					alusrc_ex  <= #`mydelay alusrc_h;
					funct_ex   <= #`mydelay funct_id;
					branch_e   <= #`mydelay branch_h;
					branchne_e <= #`mydelay branchne_h;
					memwrite_e <= #`mydelay memwrite_h;
					memtoreg_e <= #`mydelay memtoreg_h;
					regwrite_e <= #`mydelay regwrite_h;
					jump_e     <= #`mydelay jump_h;
					jal_e      <= #`mydelay jal_h;
					shiftl16_e <= #`mydelay shiftl16_h;
            end
    end
endmodule

module EXMEM_CON(input                clk, reset,   // memtoreg & regwrite & branch & memwrite after EX/MEM
                   input              memtoreg_e, regwrite_e, memwrite_e,
					    output reg   		  memtoreg_m, regwrite_m,
						 output reg  		  memwrite);
	   always @(posedge clk or posedge reset)  
    begin
         if (reset) 
            begin
					memwrite   <= #`mydelay 1'b0;
					memtoreg_m <= #`mydelay 1'b0;
					regwrite_m <= #`mydelay 1'b0;
            end
         else
            begin
					memwrite   <= #`mydelay memwrite_e;
					memtoreg_m <= #`mydelay memtoreg_e;
					regwrite_m <= #`mydelay regwrite_e;
            end
    end
endmodule

module MEMWB_CON(input        clk, reset,   // memtoreg & regwrite after MEM/WB
                    input        memtoreg_m,
						  input        regwrite_m,
					     output reg   memtoreg_w,
						  output reg   regwrite_w);
	   always @(posedge clk or posedge reset)  
    begin
         if (reset) 
            begin
               memtoreg_w <= #`mydelay 1'b0;
					regwrite_w <= #`mydelay 1'b0;
            end
         else
            begin
               memtoreg_w <= #`mydelay memtoreg_m;
					regwrite_w <= #`mydelay regwrite_m;
            end
    end
endmodule

module maindec(input  [5:0] op,
               output       signext,
               output       shiftl16,
               output       memtoreg, memwrite_m,
               output       branch, branchne, alusrc,
               output       regdst,
				   output       regwrite,
               output       jump,
					output       jal,
               output [1:0] aluop);

  reg [12:0] controls;

  assign {signext, shiftl16, regwrite, regdst, alusrc, branch, branchne, memwrite_m,
          memtoreg, jump, jal, aluop} = controls;

  always @(*)
    case(op)
      6'b000000: controls <= #`mydelay 13'b0011000000011; // Rtype
      6'b100011: controls <= #`mydelay 13'b1010100010000; // LW
      6'b101011: controls <= #`mydelay 13'b1000100100000; // SW
      6'b000100: controls <= #`mydelay 13'b1000010000001; // BEQ
		6'b000101: controls <= #`mydelay 13'b1000001000001; // BNE
      6'b001000, 
      6'b001001: controls <= #`mydelay 13'b1010100000000; // ADDI, ADDIU: only difference is exception
      6'b001101: controls <= #`mydelay 13'b0010100000010; // ORI
      6'b001111: controls <= #`mydelay 13'b0110100000000; // LUI
      6'b000010: controls <= #`mydelay 13'b0000000001000; // J
		6'b000011: controls <= #`mydelay 13'b0010000001100; // JAL
      default:   controls <= #`mydelay 13'bxxxxxxxxxxxxx; // ???
    endcase

endmodule

module aludec(input      [5:0] funct,
              input      [1:0] aluop_e,
              output reg [2:0] alucontrol);

  always @(*)
    case(aluop_e)
      2'b00: alucontrol <= #`mydelay 3'b010;  // add
      2'b01: alucontrol <= #`mydelay 3'b110;  // sub
      2'b10: alucontrol <= #`mydelay 3'b001;  // or
      default: case(funct)          // RTYPE
			 6'b001000: alucontrol <= #`mydelay 3'b011; // JR
			 6'b100000,
          6'b100001: alucontrol <= #`mydelay 3'b010; // ADD, ADDU: only difference is exception
          6'b100010,
          6'b100011: alucontrol <= #`mydelay 3'b110; // SUB, SUBU: only difference is exception
          6'b100100: alucontrol <= #`mydelay 3'b000; // AND
          6'b100101: alucontrol <= #`mydelay 3'b001; // OR
          6'b101010: alucontrol <= #`mydelay 3'b111; // SLT
			 6'b101011: alucontrol <= #`mydelay 3'b111; // SLTU
          default:   alucontrol <= #`mydelay 3'bxxx; // ???
        endcase
    endcase
    
endmodule

module datapath(input               clk, reset,
                input               signext_h,
                input               shiftl16_e,
                input               memtoreg_w, pcsrc,
                input               alusrc_ex, regdst_e, memtoreg_e,
                input               regwrite_w, regwrite_m, jump_e, jal_e, 
					 input               branch_e, branchne_e,
                input  [2:0]        alucontrol,
					 output [31:0]       pc, 
                output              zero,
                input  [31:0]       instr,
					 output [31:0]       instr_d,
					 output [31:0]       aluout_m, 
					 output [31:0]       writedata_m,
					 output              hazardcon, 
                input  [31:0]       readdata);

  wire [4:0]  writereg, writereg1, writereg_m, writereg_w;
  wire [31:0] pcnext, pcnext1, pcnextbr, pcbranch;
  wire [31:0] signimm, signimm_e, signimmsh, shiftedimm;
  wire [31:0] srca, srca_e, srcb, srca_f, srcb_f, srcb_k, srca_f1, writedata_f1;
  wire [31:0] result, result1;
  wire [31:0] writedata, writedata_e, readdata_w;
  wire [31:0] aluout, pc_d, instr_e, pc_e;
  wire        shift, PCWrite, IFIDWrite, Flush; 
  wire [31:0] pcplus4, aluout_w; 
  wire [1:0]  forwardA, forwardB;
  wire        forwardA1, forwardB1;
  
  IFID II(                           // IFID flipflop 
	 .clk        (clk),
    .reset      (reset),
	 .pcplus4    (pcplus4),
	 .pc_d       (pc_d),
	 .instr      (instr),
	 .IFIDWrite  (IFIDWrite),
	 .Flush      (Flush),
	 .instr_d    (instr_d));
  
  forwarding_unit1 fu1(                  // forwarding_unit1
    .writereg_m   (writereg_m),
    .writereg_w   (writereg_w),
    .idex_rs      (instr_e[25:21]),
    .idex_rt      (instr_e[20:16]),
	 .regwrite_m   (regwrite_m),
    .regwrite_w   (regwrite_w),
	 .forwardA     (forwardA),
	 .forwardB     (forwardB));
	 
	 forwarding_unit2 fu2(                 // forwarding_unit2
    .writereg_w   (writereg_w),
    .ifid_rs      (instr_d[25:21]),
    .ifid_rt      (instr_d[20:16]),
    .regwrite_w   (regwrite_w),
	 .forwardA1    (forwardA1),
	 .forwardB1    (forwardB1));
  
  hazard_unit hu(                     // hazard detection unit
    .ifid_rs      (instr_d[25:21]),
    .ifid_rt      (instr_d[20:16]),
	 .idex_rt      (instr_e[20:16]),
    .memtoreg_e   (memtoreg_e),
	 .PCWrite      (PCWrite),
	 .IFIDWrite    (IFIDWrite),
	 .hazardcon    (hazardcon));
	 
  flush_unit fu(                     // flush detection unit
    .srca         (srca),
    .writedata    (writedata),
	 .jump_e       (jump_e),
	 .jal_e        (jal_e),
	 .branch_e     (branch_e),
    .branchne_e   (branchne_e),
	 .Flush        (Flush));
	 
  IDEX IE(                            // srca, writedata, signimm, instr_d after ID/EX
    .clk      		   (clk),
    .reset      		(reset),
	 .Flush           (Flush),
	 .srca_e     		(srca_e),
	 .srca_f1	 		(srca_f1),
	 .writedata_e     (writedata_e),
	 .writedata_f1    (writedata_f1),
	 .signimm_e       (signimm_e),
	 .signimm         (signimm),
	 .instr_e         (instr_e),
	 .instr_d         (instr_d)); 
	 
	 EXMEM EM(                          // ALU result, DataB, rd/rt(by Regdst) after EX/MEM
    .clk               (clk), 
    .reset             (reset),
	 .aluout            (result),
	 .aluout_m          (aluout_m),
	 .srcb_f            (srcb_f),
	 .writedata_m       (writedata_m),
	 .writereg          (writereg),
	 .writereg_m        (writereg_m));
	 
	 MEMWB MW(                          // readdata, rd/rt(by Regdst), ALU result after MEM/WB
    .clk               (clk), 
    .reset             (reset),
	 .readdata          (readdata),
	 .readdata_w        (readdata_w),
	 .writereg_m        (writereg_m),
	 .writereg_w        (writereg_w),
	 .aluout_m          (aluout_m),
	 .aluout_w          (aluout_w));
	
  flopr #(32) pcreg(                     // next PC logic
    .clk     (clk),
    .reset   (reset),
	 .PCWrite (PCWrite),
    .d       (pcnext),
    .q       (pc));
  
  adder pcadd1(
    .a (pc),
    .b (32'b100),
    .y (pcplus4));

  sl2 immsh(
    .a (signimm_e),
    .y (signimmsh));
				 
  adder pcadd2(
    .a (pc_d),
    .b (signimmsh),
    .y (pcbranch));
	 
  mux2 #(32) pcbrmux(
    .d0  (pcplus4),
    .d1  (pcbranch),
    .s   (pcsrc),
    .y   (pcnextbr));

  mux2 #(32) pcmux(
    .d0   (pcnextbr),
    .d1   ({pcplus4[31:28], instr_e[25:0], 2'b00}),
    .s    (jump_e),
    .y    (pcnext1));
	 
  mux3 #(32) pcjrmux(
    .d0   (aluout),
	 .d1   (pcnext1),
	 .s    (alucontrol[2:0]),
	 .y    (pcnext));

  // register file logic
  regfile rf(
    .clk     (clk),
    .we      (regwrite_w),
    .ra1     (instr_d[25:21]),
    .ra2     (instr_d[20:16]),
    .wa      (writereg_w),
    .wd      (result1),
    .rd1     (srca),
    .rd2     (writedata));

  mux2 #(5) wrmux(
    .d0  (instr_e[20:16]),
    .d1  (instr_e[15:11]),
    .s   (regdst_e),
    .y   (writereg1));
  
  mux2 #(5) wrmux2(
    .d0  (writereg1),
	 .d1  (5'b11111),
	 .s   (jal_e),
	 .y   (writereg));	 
	 
  mux2 #(32) resmux(
    .d0 (aluout_w),
    .d1 (readdata_w),
    .s  (memtoreg_w),
    .y  (result1));	 
	 
  mux2 #(32) resmux2(
    .d0 (aluout),
	 .d1 (pcplus4),
	 .s  (jal_e),
	 .y  (result));	 
	 
  sign_zero_ext sze(
    .a         (instr_d[15:0]),
    .signext_h (signext_h),
    .y         (signimm[31:0]));

  shift_left_16 sl16(
    .a           (signimm_e[31:0]),
    .shiftl16_e  (shiftl16_e),
    .y           (shiftedimm[31:0]));

  // ALU logic
  mux2 #(32) srcbmux(
    .d0 (srcb_f),
    .d1 (shiftedimm[31:0]),
    .s  (alusrc_ex),
    .y  (srcb_k));
	 
  mux2 #(32) fumux1(
    .d0 (srca),
    .d1 (result1),
    .s  (forwardA1),
    .y  (srca_f1));
	 
  mux2 #(32) fumux2(
    .d0 (writedata),
    .d1 (result1),
    .s  (forwardB1),
    .y  (writedata_f1));
	
  mux4 #(32) alumux1(                // mux before ALU src1
    .d0 (srca_e),
	 .d1 (result1),
	 .d2 (aluout_m),
	 .s  (forwardA),
	 .y  (srca_f));
    
  mux4 #(32) alumux2(                // mux before ALU src2
    .d0 (writedata_e),
	 .d1 (result1),
	 .d2 (aluout_m),
	 .s  (forwardB),
	 .y  (srcb_f));
  
  alu alu(
    .a         (srca_f),
    .b         (srcb_k),
    .alucont   (alucontrol),
    .result    (aluout),
    .zero      (zero));	 
endmodule
  
module MEMWB(input              clk, reset,          // readdata, rd/rt(by Regdst), ALU result after MEM/WB
             input      [31:0]  readdata, aluout_m,
				 input      [4:0]   writereg_m,
				 output reg [31:0]  readdata_w, aluout_w,
				 output reg [4:0]   writereg_w);
	  always @(posedge clk or posedge reset)  
    begin
         if (reset) 
            begin
               readdata_w <= #`mydelay 32'b0;
					writereg_w <= #`mydelay 5'b0;
					aluout_w <= #`mydelay 32'b0;
            end
         else
            begin
               readdata_w <= #`mydelay readdata;
					writereg_w <= #`mydelay writereg_m;
					aluout_w <= #`mydelay aluout_m;
            end
    end
endmodule
  
module EXMEM(input              clk, reset,        // ALU result, DataB, rd/rt(by Regdst) after EX/MEM
             input      [31:0]  aluout, srcb_f,
				 input      [4:0]   writereg,
				 output reg [31:0]  aluout_m, writedata_m,
				 output reg [4:0]   writereg_m);
	  always @(posedge clk or posedge reset)  
    begin
         if (reset) 
            begin
					aluout_m <= #`mydelay 32'b0;
					writedata_m <= #`mydelay 32'b0;
					writereg_m <= #`mydelay 5'b0;
            end
         else
            begin
					aluout_m <= #`mydelay aluout;
					writedata_m <= #`mydelay srcb_f;
					writereg_m <= #`mydelay writereg;
            end
    end	 
endmodule

module IDEX(input              clk, reset, Flush,                       // srca, writedata, signimm, instr_d after ID/EX
            input      [31:0]  srca_f1, writedata_f1, signimm, instr_d,
				output reg [31:0]  srca_e, writedata_e, signimm_e, instr_e);
	always @(posedge clk or posedge reset)  
    begin
         if (reset) 
            begin
					srca_e <= #`mydelay 32'b0;
					writedata_e <= #`mydelay 32'b0;
					signimm_e <= #`mydelay 32'b0;
					instr_e <= #`mydelay 32'b0;
            end
         else
            begin
					if(~Flush)
						begin
							srca_e <= #`mydelay srca_f1;
							writedata_e <= #`mydelay writedata_f1;
							signimm_e <= #`mydelay signimm;
							instr_e <= #`mydelay instr_d;
						end
            end
    end 
endmodule

  
module IFID(input               clk, reset, 
            input               IFIDWrite, Flush,
            input        [31:0] instr,
				input        [31:0] pcplus4,
				output reg   [31:0] instr_d,
				output reg   [31:0] pc_d);
 
  always @(posedge clk or posedge reset)
  begin
       if(reset)
		 begin
		           instr_d  <= #`mydelay 32'b0;
					  pc_d     <= #`mydelay 32'b0;
					  
		 end
		 else
				begin
					if(~IFIDWrite && ~Flush)
						begin
							instr_d  <= #`mydelay instr;
							pc_d     <= #`mydelay pcplus4;
						end
				end
  end
endmodule 


module forwarding_unit1(input [4:0]       writereg_m, writereg_w,    // forwarding unit1
                        input             regwrite_m, regwrite_w,
			input [4:0]       idex_rs, idex_rt, 
			output reg [1:0]  forwardA, forwardB);
   always @(*)						 
	begin
   if (regwrite_m && (writereg_m==idex_rs))
        forwardA <= #`mydelay 2'b10;
	else if (regwrite_w && (writereg_w==idex_rs))
        forwardA <= #`mydelay 2'b01;
	else
        forwardA <= #`mydelay 2'b00;
	if (regwrite_m && (writereg_m==idex_rt))
	     forwardB <= #`mydelay 2'b10;
	else if (regwrite_w && (writereg_w==idex_rt))
		  forwardB <= #`mydelay 2'b01;
	else
		  forwardB <= #`mydelay 2'b00;
   end
endmodule

module forwarding_unit2(input [4:0]        writereg_w,                  // forwarding unit2
                        input              regwrite_w,
			input [4:0]        ifid_rs, ifid_rt, 
			output reg         forwardA1, forwardB1);
   always @(*)						 
	begin
   if (regwrite_w && (writereg_w==ifid_rs))
        forwardA1 <= #`mydelay 1'b1;
	else
	     forwardA1 <= #`mydelay 1'b0; 
   if (regwrite_w && (writereg_w==ifid_rt))
		  forwardB1 <= #`mydelay 1'b1;
	else		   
		  forwardB1 <= #`mydelay 1'b0;
			
   end  
endmodule

module hazard_unit(input  memtoreg_e,                         // hazard detection unit
		   input [4:0]		 ifid_rs, ifid_rt, idex_rt,
	           output reg 		 PCWrite, IFIDWrite, hazardcon);
   always @(*)
	begin
   if (memtoreg_e && ((idex_rt==ifid_rs) || (idex_rt==ifid_rt)))
	  begin
	     PCWrite   <= #`mydelay 1'b1;
		  IFIDWrite <= #`mydelay 1'b1;
		  hazardcon <= #`mydelay 1'b1;
	  end
	else
	  begin
	     PCWrite   <= #`mydelay 1'b0;
		  IFIDWrite <= #`mydelay 1'b0;
		  hazardcon <= #`mydelay 1'b0;
	  end
	 end
endmodule

module flush_unit(input	 [31:0]	    srca, writedata,                       // Flush detection unit
						input              branch_e, branchne_e, jump_e, jal_e,
						output reg 		    Flush);
   always @(*)
	begin
   if ((branch_e && (srca == writedata)) || (branchne_e && srca != writedata) || jump_e || jal_e)
	  begin
	     Flush   <= #`mydelay 1'b1;
	  end
	else
	  begin
	     Flush   <= #`mydelay 1'b0;
	  end
	 end
endmodule
