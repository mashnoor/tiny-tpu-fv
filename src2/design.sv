`timescale 1ns/1ps
`default_nettype none

// -------- merged from fixedpoint.sv --------
// Modules : fxp_zoom, fxp_add, fxp_addsub, fxp_mul, fxp_mul_pipe, fxp_div, fxp_div_pipe, fxp_sqrt, fxp_sqrt_pipe, fxp2float, fxp2float_pipe, float2fxp, float2fxp_pipe
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: fixed-point library
//--------------------------------------------------------------------------------------------------------






//--------------------------------------------------------------------------------------------------------
// Module  : fxp_zoom
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: bit width conversion for fixed-point
//           combinational logic
//--------------------------------------------------------------------------------------------------------

module fxp_zoom #(
    parameter WII  = 8,
    parameter WIF  = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire [WII+WIF-1:0] in,
    output wire [WOI+WOF-1:0] out,
    output reg                overflow
);

initial overflow = 1'b0;

reg [WII+WOF-1:0] inr = 0;
reg [WII-1:0] ini = 0;
reg [WOI-1:0] outi = 0;
reg [WOF-1:0] outf = 0;

generate if(WOF<WIF) begin
    if(ROUND==0) begin
        always @ (*) inr = in[WII+WIF-1:WIF-WOF];
    end else if(WII+WOF>=2) begin
        always @ (*) begin
            inr = in[WII+WIF-1:WIF-WOF];
            if(in[WIF-WOF-1] & ~(~inr[WII+WOF-1] & (&inr[WII+WOF-2:0]))) inr=inr+1;
        end
    end else begin
        always @ (*) begin
            inr = in[WII+WIF-1:WIF-WOF];
            if(in[WIF-WOF-1] & inr[WII+WOF-1]) inr=inr+1;
        end
    end
end else if(WOF==WIF) begin
    always @ (*) inr[WII+WOF-1:WOF-WIF] = in;
end else begin
    always @ (*) begin
        inr[WII+WOF-1:WOF-WIF] = in;
        inr[WOF-WIF-1:0] = 0;
    end
end endgenerate


generate if(WOI<WII) begin
    always @ (*) begin
        {ini, outf} = inr;
        if         ( ~ini[WII-1] & |ini[WII-2:WOI-1] ) begin
            overflow = 1'b1;
            outi = {WOI{1'b1}};
            outi[WOI-1] = 1'b0;
            outf = {WOF{1'b1}};
        end else if(  ini[WII-1] & ~(&ini[WII-2:WOI-1]) ) begin
            overflow = 1'b1;
            outi = 0;
            outi[WOI-1] = 1'b1;
            outf = 0;
        end else begin
            overflow = 1'b0;
            outi = ini[WOI-1:0];
        end
    end
end else begin
    always @ (*) begin
        {ini, outf} = inr;
        overflow = 1'b0;
        outi = ini[WII-1] ? {WOI{1'b1}} : 0;
        outi[WII-1:0] = ini;
    end
end endgenerate

assign out = {outi, outf};

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_add
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: addition
//           combinational logic
//--------------------------------------------------------------------------------------------------------

module fxp_add # (
    parameter WIIA = 8,
    parameter WIFA = 8,
    parameter WIIB = 8,
    parameter WIFB = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire [WIIA+WIFA-1:0] ina,
    input  wire [WIIB+WIFB-1:0] inb,
    output wire [WOI +WOF -1:0] out,
    output wire                 overflow
);

localparam WII = WIIA>WIIB ? WIIA : WIIB;
localparam WIF = WIFA>WIFB ? WIFA : WIFB;
localparam WRI = WII + 1;
localparam WRF = WIF;

wire [WII+WIF-1:0] inaz, inbz;

wire signed [WRI+WRF-1:0] res = $signed(inaz) + $signed(inbz);

fxp_zoom # (
    .WII      ( WIIA     ),
    .WIF      ( WIFA     ),
    .WOI      ( WII      ),
    .WOF      ( WIF      ),
    .ROUND    ( 0        )
) ina_zoom (
    .in       ( ina      ),
    .out      ( inaz     ),
    .overflow (          )
);

fxp_zoom # (
    .WII      ( WIIB     ),
    .WIF      ( WIFB     ),
    .WOI      ( WII      ),
    .WOF      ( WIF      ),
    .ROUND    ( 0        )
) inb_zoom (
    .in       ( inb      ),
    .out      ( inbz     ),
    .overflow (          )
);

fxp_zoom # (
    .WII      ( WRI            ),
    .WIF      ( WRF            ),
    .WOI      ( WOI            ),
    .WOF      ( WOF            ),
    .ROUND    ( ROUND          )
) res_zoom (
    .in       ( $unsigned(res) ),
    .out      ( out            ),
    .overflow ( overflow       )
);

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_addsub
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: addition and subtraction
//           combinational logic
//--------------------------------------------------------------------------------------------------------

module fxp_addsub # (
    parameter WIIA = 8,
    parameter WIFA = 8,
    parameter WIIB = 8,
    parameter WIFB = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire [WIIA+WIFA-1:0] ina,
    input  wire [WIIB+WIFB-1:0] inb,
    input  wire                 sub, // 0=add, 1=sub
    output wire [WOI +WOF -1:0] out,
    output wire                 overflow
);

localparam WIIBE = WIIB + 1;
localparam   WII = WIIA>WIIBE ? WIIA : WIIBE;
localparam   WIF = WIFA>WIFB  ? WIFA : WIFB;
localparam   WRI = WII + 1;
localparam   WRF = WIF;

localparam [WIIBE+WIFB-1:0] ONE = 1;
wire [WIIBE+WIFB-1:0] inbe;
wire [   WII+WIF-1:0] inaz, inbz;
wire [WIIBE+WIFB-1:0] inbv = sub ? (~inbe)+ONE : inbe;
wire signed [WRI+WRF-1:0] res = $signed(inaz) + $signed(inbz);

fxp_zoom # (
    .WII      ( WIIB     ),
    .WIF      ( WIFB     ),
    .WOI      ( WIIBE    ),
    .WOF      ( WIFB     ),
    .ROUND    ( 0        )
) inb_extend (
    .in       ( inb      ),
    .out      ( inbe     ),
    .overflow (          )
);

fxp_zoom # (
    .WII      ( WIIA     ),
    .WIF      ( WIFA     ),
    .WOI      ( WII      ),
    .WOF      ( WIF      ),
    .ROUND    ( 0        )
) ina_zoom (
    .in       ( ina      ),
    .out      ( inaz     ),
    .overflow (          )
);

fxp_zoom # (
    .WII      ( WIIBE    ),
    .WIF      ( WIFB     ),
    .WOI      ( WII      ),
    .WOF      ( WIF      ),
    .ROUND    ( 0        )
) inb_zoom (
    .in       ( inbv     ),
    .out      ( inbz     ),
    .overflow (          )
);

fxp_zoom # (
    .WII      ( WRI            ),
    .WIF      ( WRF            ),
    .WOI      ( WOI            ),
    .WOF      ( WOF            ),
    .ROUND    ( ROUND          )
) res_zoom (
    .in       ( $unsigned(res) ),
    .out      ( out            ),
    .overflow ( overflow       )
);

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_mul
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: multiplication
//           combinational logic
//--------------------------------------------------------------------------------------------------------

module fxp_mul # (
    parameter WIIA = 8,
    parameter WIFA = 8,
    parameter WIIB = 8,
    parameter WIFB = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire [WIIA+WIFA-1:0] ina,
    input  wire [WIIB+WIFB-1:0] inb,
    output wire [WOI +WOF -1:0] out,
    output wire                 overflow
);

localparam WRI = WIIA + WIIB;
localparam WRF = WIFA + WIFB;

wire signed [WRI+WRF-1:0] res = $signed(ina) * $signed(inb);

fxp_zoom # (
    .WII      ( WRI            ),
    .WIF      ( WRF            ),
    .WOI      ( WOI            ),
    .WOF      ( WOF            ),
    .ROUND    ( ROUND          )
) res_zoom (
    .in       ( $unsigned(res) ),
    .out      ( out            ),
    .overflow ( overflow       )
);

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_mul_pipe
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: multiplication
//           pipeline stage = 2
//--------------------------------------------------------------------------------------------------------

module fxp_mul_pipe # (
    parameter WIIA = 8,
    parameter WIFA = 8,
    parameter WIIB = 8,
    parameter WIFB = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire                 rstn,
    input  wire                 clk,
    input  wire [WIIA+WIFA-1:0] ina,
    input  wire [WIIB+WIFB-1:0] inb,
    output reg  [WOI +WOF -1:0] out,
    output reg                  overflow
);

initial {out, overflow} = 0;

localparam WRI = WIIA + WIIB;
localparam WRF = WIFA + WIFB;

wire [WOI +WOF -1:0] outc;
wire                 overflowc;

reg signed [WRI+WRF-1:0] res = 0;

always @ (posedge clk or negedge rstn)
    if(~rstn)
        res <= 0;
    else
        res <= $signed(ina) * $signed(inb);

fxp_zoom # (
    .WII      ( WRI            ),
    .WIF      ( WRF            ),
    .WOI      ( WOI            ),
    .WOF      ( WOF            ),
    .ROUND    ( ROUND          )
) res_zoom (
    .in       ( $unsigned(res) ),
    .out      ( outc           ),
    .overflow ( overflowc      )
);

always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        out      <= 0;
        overflow <= 1'b0;
    end else begin
        out      <= outc;
        overflow <= overflowc;
    end

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_div
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: division
//           combinational logic
//           not recommended due to the long critical path
//--------------------------------------------------------------------------------------------------------

module fxp_div #(
    parameter WIIA = 8,
    parameter WIFA = 8,
    parameter WIIB = 8,
    parameter WIFB = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire [WIIA+WIFA-1:0] dividend,
    input  wire [WIIB+WIFB-1:0] divisor,
    output reg  [WOI +WOF -1:0] out,
    output reg                  overflow
);

initial {out, overflow} = 0;

localparam WRI = WOI+WIIB > WIIA ? WOI+WIIB : WIIA;
localparam WRF = WOF+WIFB > WIFA ? WOF+WIFB : WIFA;

reg                  sign = 1'b0;
reg  [WIIA+WIFA-1:0] udividend = 0;
reg  [WIIB+WIFB-1:0]  udivisor = 0;
reg  [ WRI+ WRF-1:0] acc=0, acct=0;
wire [ WRI+ WRF-1:0] divd, divr;

localparam  [WIIA+WIFA-1:0] ONEA = 1;
localparam  [WIIB+WIFB-1:0] ONEB = 1;
localparam  [WOI + WOF-1:0] ONEO = 1;

always @ (*) begin  // convert dividend and divisor to positive number
    sign      = dividend[WIIA+WIFA-1] ^ divisor[WIIB+WIFB-1];
    udividend = dividend[WIIA+WIFA-1] ? (~dividend)+ONEA : dividend;
    udivisor  =  divisor[WIIB+WIFB-1] ? (~ divisor)+ONEB : divisor ;
end

fxp_zoom # (
    .WII      ( WIIA      ),
    .WIF      ( WIFA      ),
    .WOI      ( WRI       ),
    .WOF      ( WRF       ),
    .ROUND    ( 0         )
) dividend_zoom (
    .in       ( udividend ),
    .out      ( divd      ),
    .overflow (           )
);

fxp_zoom # (
    .WII      ( WIIB      ),
    .WIF      ( WIFB      ),
    .WOI      ( WRI       ),
    .WOF      ( WRF       ),
    .ROUND    ( 0         )
)  divisor_zoom (
    .in       ( udivisor  ),
    .out      ( divr      ),
    .overflow (           )
);

integer shamt;

always @ (*) begin
    acc = 0;
    for(shamt=WOI-1; shamt>=-WOF; shamt=shamt-1) begin
        if(shamt>=0)
            acct = acc + (divr<<shamt);
        else
            acct = acc + (divr>>(-shamt));
        if( acct <= divd ) begin
            acc = acct;
            out[WOF+shamt] = 1'b1;
        end else
            out[WOF+shamt] = 1'b0;
    end
    
    if(ROUND && ~(&out)) begin
        acct = acc+(divr>>(WOF));
        if(acct-divd<divd-acc)
            out=out+1;
    end
    
    overflow = 1'b0;
    if(sign) begin
        if(out[WOI+WOF-1]) begin
            if(|out[WOI+WOF-2:0]) overflow = 1'b1;
            out[WOI+WOF-1] = 1'b1;
            out[WOI+WOF-2:0] = 0;
        end else begin
            out = (~out) + ONEO;
        end
    end else begin
        if(out[WOI+WOF-1]) begin
            overflow = 1'b1;
            out[WOI+WOF-1] = 1'b0;
            out[WOI+WOF-2:0] = {(WOI+WOF){1'b1}};
        end
    end
end

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_div_pipe
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: division
//           pipeline stage = WOI+WOF+3
//--------------------------------------------------------------------------------------------------------

module fxp_div_pipe #(
    parameter WIIA = 8,
    parameter WIFA = 8,
    parameter WIIB = 8,
    parameter WIFB = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire                 rstn,
    input  wire                 clk,
    input  wire [WIIA+WIFA-1:0] dividend,
    input  wire [WIIB+WIFB-1:0] divisor,
    output reg  [WOI +WOF -1:0] out,
    output reg                  overflow
);

initial {out, overflow} = 0;

localparam WRI = WOI+WIIB > WIIA ? WOI+WIIB : WIIA;
localparam WRF = WOF+WIFB > WIFA ? WOF+WIFB : WIFA;

wire [WRI+WRF-1:0]  divd, divr;
reg  [WOI+WOF-1:0] roundedres = 0;
reg                rsign = 1'b0;
reg                 sign [WOI+WOF:0];
reg  [WRI+WRF-1:0]  acc  [WOI+WOF:0];
reg  [WRI+WRF-1:0] divdp [WOI+WOF:0];
reg  [WRI+WRF-1:0] divrp [WOI+WOF:0];
reg  [WOI+WOF-1:0]  res  [WOI+WOF:0];
localparam  [WOI+WOF-1:0] ONEO = 1;

integer ii;

// initialize all regs
initial for(ii=0; ii<=WOI+WOF; ii=ii+1) begin
            res  [ii] = 0;
            divrp[ii] = 0;
            divdp[ii] = 0;
            acc  [ii] = 0;
            sign [ii] = 1'b0;
        end

wire [WIIA+WIFA-1:0] ONEA = 1;
wire [WIIB+WIFB-1:0] ONEB = 1;

// convert dividend and divisor to positive number
wire [WIIA+WIFA-1:0] udividend = dividend[WIIA+WIFA-1] ? (~dividend)+ONEA : dividend;
wire [WIIB+WIFB-1:0]  udivisor =  divisor[WIIB+WIFB-1] ? (~ divisor)+ONEB : divisor ;

fxp_zoom # (
    .WII      ( WIIA      ),
    .WIF      ( WIFA      ),
    .WOI      ( WRI       ),
    .WOF      ( WRF       ),
    .ROUND    ( 0         )
) dividend_zoom (
    .in       ( udividend ),
    .out      ( divd      ),
    .overflow (           )
);

fxp_zoom # (
    .WII      ( WIIB      ),
    .WIF      ( WIFB      ),
    .WOI      ( WRI       ),
    .WOF      ( WRF       ),
    .ROUND    ( 0         )
)  divisor_zoom (
    .in       ( udivisor  ),
    .out      ( divr      ),
    .overflow (           )
);

// 1st pipeline stage: convert dividend and divisor to positive number
always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        res[0]   <= 0;
        acc[0]   <= 0;
        divdp[0] <= 0;
        divrp[0] <= 0;
        sign [0] <= 1'b0;
    end else begin
        res[0]   <= 0;
        acc[0]   <= 0;
        divdp[0] <= divd;
        divrp[0] <= divr;
        sign [0] <= dividend[WIIA+WIFA-1] ^ divisor[WIIB+WIFB-1];
    end

reg [WRI+ WRF-1:0] tmp;

// from 2nd to WOI+WOF+1 pipeline stages: calculate division
always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        for(ii=0; ii<WOI+WOF; ii=ii+1) begin
            res  [ii+1] <= 0;
            divrp[ii+1] <= 0;
            divdp[ii+1] <= 0;
            acc  [ii+1] <= 0;
            sign [ii+1] <= 1'b0;
        end
    end else begin
        for(ii=0; ii<WOI+WOF; ii=ii+1) begin
            
            res  [ii+1] <= res[ii];
            divdp[ii+1] <= divdp[ii];
            divrp[ii+1] <= divrp[ii];
            sign [ii+1] <= sign [ii];
            if(ii<WOI)
                tmp = acc[ii] + (divrp[ii]<<(WOI-1-ii));
            else
                tmp = acc[ii] + (divrp[ii]>>(1+ii-WOI));
            if( tmp < divdp[ii] ) begin
                acc[ii+1] <= tmp;
                res[ii+1][WOF+WOI-1-ii] <= 1'b1;
            end else begin
                acc[ii+1] <= acc[ii];
                res[ii+1][WOF+WOI-1-ii] <= 1'b0;
            end
        end
    end

// next pipeline stage: process round
always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        roundedres <= 0;
        rsign      <= 1'b0;
    end else begin
        if( ROUND && ~(&res[WOI+WOF]) && (acc[WOI+WOF]+(divrp[WOI+WOF]>>(WOF))-divdp[WOI+WOF]) < (divdp[WOI+WOF]-acc[WOI+WOF]) )
            roundedres <= res[WOI+WOF] + ONEO;
        else
            roundedres <= res[WOI+WOF];
        rsign      <= sign[WOI+WOF];
    end

// the last pipeline stage: process roof and output
always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        overflow <= 1'b0;
        out <= 0;
    end else begin
        overflow <= 1'b0;
        if(rsign) begin
            if(roundedres[WOI+WOF-1]) begin
                if(|roundedres[WOI+WOF-2:0]) overflow <= 1'b1;
                out[WOI+WOF-1] <= 1'b1;
                out[WOI+WOF-2:0] <= 0;
            end else
                out <= (~roundedres) + ONEO;
        end else begin
            if(roundedres[WOI+WOF-1]) begin
                overflow <= 1'b1;
                out[WOI+WOF-1] <= 1'b0;
                out[WOI+WOF-2:0] <= {(WOI+WOF){1'b1}};
            end else
                out <= roundedres;
        end
    end

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_sqrt
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: square root
//           combinational logic
//           not recommended due to the long critical path
//--------------------------------------------------------------------------------------------------------

module fxp_sqrt #(
    parameter WII  = 8,
    parameter WIF  = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire [WII+WIF-1:0] in,
    output wire [WOI+WOF-1:0] out,
    output wire               overflow
);

localparam WTI = (WII%2==1) ? WII+1 : WII;
localparam WRI = WTI/2;

localparam [WII+WIF-1:0] ONEI = 1;
localparam [WTI+WIF-1:0] ONET = 1;
localparam [WRI+WIF-1:0] ONER = 1;

reg [WRI+WIF:0] resushort = 0;

integer ii;

reg                sign;
reg  [WTI+WIF-1:0] inu, resu2, resu2tmp, resu;

always @ (*) begin
    sign = in[WII+WIF-1];
    inu = 0;
    inu[WII+WIF-1:0] = sign ? (~in)+ONEI : in;
    {resu2,resu} = 0;
    for(ii=WRI-1; ii>=-WIF; ii=ii-1) begin
        resu2tmp = resu2;
        if(ii>=0) resu2tmp = resu2tmp + (resu<<( 1+ii));
        else      resu2tmp = resu2tmp + (resu>>(-1-ii));
        if(2*ii+WIF>=0) resu2tmp = resu2tmp + ( ONET << (2*ii+WIF) );
        if(resu2tmp<=inu && inu!=0) begin
            resu[ii+WIF] = 1'b1;
            resu2 = resu2tmp;
        end
    end
    resushort = sign ? (~resu[WRI+WIF:0])+ONER : resu[WRI+WIF:0];
end

fxp_zoom # (
    .WII      ( WRI+1          ),
    .WIF      ( WIF            ),
    .WOI      ( WOI            ),
    .WOF      ( WOF            ),
    .ROUND    ( ROUND          )
) res_zoom (
    .in       ( resushort      ),
    .out      ( out            ),
    .overflow ( overflow       )
);

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp_sqrt_pipe
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: square root
//           pipeline stage = [WII/2]+WIF+2, [] means upper int
//--------------------------------------------------------------------------------------------------------

module fxp_sqrt_pipe #(
    parameter WII  = 8,
    parameter WIF  = 8,
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire               rstn,
    input  wire               clk,
    input  wire [WII+WIF-1:0] in,
    output reg  [WOI+WOF-1:0] out,
    output reg                overflow
);

initial {overflow,out} = 0;

localparam WTI = (WII%2==1) ? WII+1 : WII;
localparam WRI = WTI/2;

localparam [WII+WIF-1:0] ONEI = 1;
localparam [WTI+WIF-1:0] ONET = 1;
localparam [WRI+WIF-1:0] ONER = 1;

reg               sign [WRI+WIF :0];
reg [WTI+WIF-1:0] inu  [WRI+WIF :0];
reg [WTI+WIF-1:0] resu2 [WRI+WIF :0];
reg [WTI+WIF-1:0] resu  [WRI+WIF :0];

integer ii, jj;
reg [WTI+WIF-1:0] resu2tmp;

initial for(ii=0; ii<=WRI+WIF; ii=ii+1) begin
            sign[ii] = 0;
            inu[ii]  = 0;
            resu2[ii]= 0;
            resu[ii] = 0;
        end

always @ (posedge clk or negedge rstn) begin
    if(~rstn) begin
        for(ii=0; ii<=WRI+WIF; ii=ii+1) begin
            sign[ii] <= 0;
            inu[ii]  <= 0;
            resu2[ii]<= 0;
            resu[ii] <= 0;
        end
    end else begin
        sign[0] <= in[WII+WIF-1];
        inu[0] <= 0;
        inu[0][WII+WIF-1:0] <= in[WII+WIF-1] ? (~in)+ONEI : in;
        resu2[0] <= 0;
        resu[0] <= 0;
        for(ii=WRI-1; ii>=-WIF; ii=ii-1) begin
            jj = WRI-1-ii;
            sign[jj+1] <= sign[jj];
            inu [jj+1] <= inu [jj];
            resu[jj+1] <= resu[jj];
            resu2[jj+1]<= resu2[jj];
            resu2tmp = resu2[jj];
            if(ii>=0)
                resu2tmp = resu2tmp + (resu[jj]<<( 1+ii));
            else
                resu2tmp = resu2tmp + (resu[jj]>>(-1-ii));
            if(2*ii+WIF>=0)
                resu2tmp = resu2tmp + ( ONET << (2*ii+WIF) );
            if(resu2tmp<=inu[jj] && inu[jj]!=0) begin
                resu[jj+1][ii+WIF] <= 1'b1;
                resu2[jj+1] <= resu2tmp;
            end
        end
    end
end

wire [WRI+WIF  :0] resushort = sign[WRI+WIF] ? (~resu[WRI+WIF][WRI+WIF:0])+ONER : resu[WRI+WIF][WRI+WIF:0];
wire [WOI+WOF-1:0] outl;
wire               overflowl;

fxp_zoom # (
    .WII      ( WRI+1          ),
    .WIF      ( WIF            ),
    .WOI      ( WOI            ),
    .WOF      ( WOF            ),
    .ROUND    ( ROUND          )
) res_zoom (
    .in       ( resushort      ),
    .out      ( outl           ),
    .overflow ( overflowl      )
);

always @ (posedge clk or negedge rstn)
    if(~rstn)
        {overflow,out} <= 0;
    else
        {overflow,out} <= {overflowl,outl};

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp2float
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: convert fixed-point to float-point (IEEE754 single precision)
//           combinational logic
//           not recommended due to the long critical path
//--------------------------------------------------------------------------------------------------------

module fxp2float #(
    parameter WII = 8,
    parameter WIF = 8
)(
    input  wire [WII+WIF-1:0] in,
    output reg         [31:0] out
);

initial out = 0;

localparam [WII+WIF-1:0] ONEI = 1;

wire  sign = in[WII+WIF-1];
wire  [WII+WIF-1:0] inu = sign ? (~in)+ONEI : in;

integer jj;
reg flag;
reg signed [9:0] expz, ii;
reg [ 7:0] expt;
reg [22:0] tail;

always @ (*) begin
    
    tail = 0;
    flag = 1'b0;
    ii = 10'd22;
    expz = 0;
    
    for(jj=WII+WIF-1; jj>=0; jj=jj-1) begin
        if(flag && ii>=0) begin
            tail[ii] = inu[jj];
            ii=ii-1;
        end
        if(inu[jj]) begin
            if(~flag) expz = jj+127-WIF;
            flag = 1'b1;
        end
    end

    if(expz<$signed(10'd255))
        expt = (inu==0) ? 0 : expz[7:0];
    else begin
        expt = 8'd254;
        tail = 23'h7FFFFF;
    end
    
    out = {sign, expt, tail};
end

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : fxp2float_pipe
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: convert fixed-point to float-point (IEEE754 single precision)
//           pipeline stage = WII+WIF+2
//--------------------------------------------------------------------------------------------------------

module fxp2float_pipe #(
    parameter WII = 8,
    parameter WIF = 8
)(
    input  wire               rstn,
    input  wire               clk,
    input  wire [WII+WIF-1:0] in,
    output wire        [31:0] out
);

reg              sign [WII+WIF :0];
reg         [9:0] exp [WII+WIF :0];
reg [WII+WIF-1:0] inu [WII+WIF :0];

localparam [WII+WIF-1:0] ONEI = 1;

reg [23:0] vall = 0;
reg [23:0] valo = 0;
reg [ 7:0] expo = 0;
reg       signo = 0;

assign out = {signo, expo, valo[22:0]};

integer ii;

initial for(ii=WII+WIF; ii>=0; ii=ii-1) begin
            sign[ii] = 0;
            exp[ii]  = 0;
            inu[ii]  = 0;
        end

always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        for(ii=WII+WIF; ii>=0; ii=ii-1) begin
            sign[ii] <= 0;
            exp[ii]  <= 0;
            inu[ii]  <= 0;
        end
    end else begin
        sign[WII+WIF] <= in[WII+WIF-1];
        exp [WII+WIF] <= WII+127-1;
        inu[WII+WIF]  <= in[WII+WIF-1] ? (~in)+ONEI : in;
        for(ii=WII+WIF-1; ii>=0; ii=ii-1) begin
            sign[ii] <= sign[ii+1];
            if(inu[ii+1][WII+WIF-1]) begin
                exp[ii] <= exp[ii+1];
                inu[ii] <= inu[ii+1];
            end else begin
                if(exp[ii+1]!=0)
                    exp[ii] <= exp[ii+1] - 10'd1;
                else
                    exp[ii] <= exp[ii+1];
                inu[ii] <=(inu[ii+1] << 1);
            end
        end
    end
    
generate if(23>WII+WIF-1) begin
    always @ (*) begin
        vall = 0;
        vall[23:23-(WII+WIF-1)] = inu[0];
    end
end else begin
    always @ (*) vall = inu[0][WII+WIF-1:WII+WIF-1-23];
end endgenerate

always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        {signo, expo, valo} <= 0;
    end else begin
        signo <= sign[0];
        if(exp[0]>=10'd255) begin
            expo <= 8'd255;
            valo <= 24'hFFFFFF;
        end else if(exp[0]==10'd0 || ~vall[23]) begin
            expo <= 8'd0;
            valo <= 0;
        end else begin
            expo <= exp[0][7:0];
            valo <= vall;
        end
    end
    
endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : float2fxp
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: convert float-point (IEEE754 single precision) to fixed-point
//           combinational logic
//           not recommended due to the long critical path
//--------------------------------------------------------------------------------------------------------

module float2fxp #(
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire        [31:0] in,
    output reg  [WOI+WOF-1:0] out,
    output reg                overflow
);

initial {out, overflow} = 0;

localparam [WOI+WOF-1:0] ONEO = 1;

integer ii;

reg        round, sign;
reg [ 7:0] exp2;
reg [23:0] val;
reg signed [31:0] expi;

always @ (*) begin
    round = 0;
    overflow = 0;
    {sign, exp2, val[22:0]} = in;
    val[23] = 1'b1;
    out = 0;
    expi = exp2-127+WOF;
    if( &exp2 )
        overflow = 1'b1;
    else if( in[30:0]!=0 ) begin
        for(ii=23; ii>=0; ii=ii-1) begin
            if(val[ii]) begin
                if(expi>=WOI+WOF-1)
                    overflow = 1'b1;
                else if(expi>=0)
                    out[expi] = 1'b1;
                else if(ROUND && expi==-1)
                    round=1'b1;
            end
            expi = expi - 1;
        end
        if(round) out=out+1;
    end
    if(overflow) begin
        if(sign) begin
            out[WOI+WOF-1]   = 1'b1;
            out[WOI+WOF-2:0] = 0;
        end else begin
            out[WOI+WOF-1]   = 1'b0;
            out[WOI+WOF-2:0] = {(WOI+WOF){1'b1}};
        end
    end else begin
        if(sign)
            out = (~out) + ONEO;
    end
end

endmodule







//--------------------------------------------------------------------------------------------------------
// Module  : float2fxp_pipe
// Type    : synthesizable
// Standard: Verilog 2001 (IEEE1364-2001)
// Function: convert float-point (IEEE754 single precision) to fixed-point
//           pipeline stage = WOI+WOF+4
//--------------------------------------------------------------------------------------------------------

module float2fxp_pipe #(
    parameter WOI  = 8,
    parameter WOF  = 8,
    parameter ROUND= 1
)(
    input  wire               rstn,
    input  wire               clk,
    input  wire        [31:0] in,
    output reg  [WOI+WOF-1:0] out,
    output reg                overflow
);

localparam [WOI+WOF-1:0] ONEO = 1;

initial {out, overflow} = 0;

// input comb
wire        sign;
wire [ 7:0] exp;
wire [23:0] val;

assign {sign,exp,val[22:0]} = in;
assign val[23] = |exp;

// pipeline stage1
reg signinit=1'b0, roundinit=1'b0;
reg signed [31:0] expinit = 0;
reg [WOI+WOF-1:0] outinit = 0;

generate if(WOI+WOF-1>=23) begin
    always @ (posedge clk or negedge rstn)
        if(~rstn) begin
            outinit <= 0;
            roundinit <= 1'b0;
        end else begin
            outinit <= 0;
            outinit[WOI+WOF-1:WOI+WOF-1-23] <= val;
            roundinit <= 1'b0;
        end
end else begin
    always @ (posedge clk or negedge rstn)
        if(~rstn) begin
            outinit <= 0;
            roundinit <= 1'b0;
        end else begin
            outinit <= val[23:23-(WOI+WOF-1)];
            roundinit <= ( ROUND && val[23-(WOI+WOF-1)-1] );
        end
end endgenerate

always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        signinit <= 1'b0;
        expinit  <= 0;
    end else begin
        signinit <= sign;
        if( exp==8'd255 || {24'd0,exp}>WOI+126 )
            expinit <= 0;
        else
            expinit <= {24'd0,exp} - (WOI-1) - 127;
    end

// next pipeline stages
reg              signs [WOI+WOF :0];
reg             rounds [WOI+WOF :0];
reg [31:0]        exps [WOI+WOF :0];
reg [WOI+WOF-1:0] outs [WOI+WOF :0];

integer ii;

always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        for(ii=0; ii<WOI+WOF+1; ii=ii+1) begin
            signs[ii]  <= 0;
            rounds[ii] <= 0;
            exps[ii]   <= 0;
            outs[ii]   <= 0;
        end
    end else begin
        for(ii=0; ii<WOI+WOF; ii=ii+1) begin
            signs[ii] <= signs[ii+1];
            if(exps[ii+1]!=0) begin
                {outs[ii], rounds[ii]} <= {       1'b0,   outs[ii+1] };
                exps[ii] <= exps[ii+1] + 1;
            end else begin
                {outs[ii], rounds[ii]} <= { outs[ii+1], rounds[ii+1] };
                exps[ii] <= exps[ii+1];
            end
        end
        signs[WOI+WOF] <= signinit;
        rounds[WOI+WOF] <= roundinit;
        exps[WOI+WOF] <= expinit;
        outs[WOI+WOF] <= outinit;
    end

// last 2nd pipeline stage
reg               signl = 1'b0;
reg [WOI+WOF-1:0] outl = 0;
reg [WOI+WOF-1:0] outt;
always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        outl <= 0;
        signl <= 1'b0;
    end else begin
        outt = outs[0];
        if(ROUND & rounds[0] & ~(&outt))
            outt = outt + 1;
        if(signs[0]) begin
            signl <= (outt!=0);
            outt  = (~outt) + ONEO;
        end else
            signl <= 1'b0;
        outl <= outt;
    end

// last 1st pipeline stage: overflow control
always @ (posedge clk or negedge rstn)
    if(~rstn) begin
        out <= 0;
        overflow <= 1'b0;
    end else begin
        out <= outl;
        overflow <= 1'b0;
        if(signl) begin
            if(~outl[WOI+WOF-1]) begin
                out[WOI+WOF-1] <= 1'b1;
                out[WOI+WOF-2:0] <= 0;
                overflow <= 1'b1;
            end
        end else begin
            if(outl[WOI+WOF-1]) begin
                out[WOI+WOF-1] <= 1'b0;
                out[WOI+WOF-2:0] <= {(WOI+WOF){1'b1}};
                overflow <= 1'b1;
            end
        end
    end

endmodule
// -------- merged from pe.sv --------

module pe #(
    parameter int DATA_WIDTH = 16 //TODO: remove? we're not using this yet, lol)
) (
    input wire logic clk,
    input wire logic rst,

    // North wires of PE
    input wire logic signed [15:0] pe_psum_in,
    input wire logic signed [15:0] pe_weight_in,
    input wire logic pe_accept_w_in,

    // West wires of PE
    input wire logic signed [15:0] pe_input_in,
    input wire logic pe_valid_in,
    input wire logic pe_switch_in,
    input wire logic pe_enabled,

    // South wires of the PE
    output var logic signed [15:0] pe_psum_out,
    output var logic signed [15:0] pe_weight_out,

    // East wires of the PE
    output var logic signed [15:0] pe_input_out,
    output var logic pe_valid_out,
    output var logic pe_switch_out
);

    logic signed [15:0] mult_out;
    wire signed [15:0] mac_out; // just a wire
    logic signed [15:0] weight_reg_active; // foreground register
    logic signed[15:0] weight_reg_inactive; // background register

    fxp_mul mult (
        .ina(pe_input_in),
        .inb(weight_reg_active),
        .out(mult_out),
        .overflow()
    );

    fxp_add adder (
        .ina(mult_out),
        .inb(pe_psum_in),
        .out(mac_out),
        .overflow()
    );

    // Only the switch flag is combinational (active register copies inactive register on the same clock cycle that switch flag is set)
    // That means inputs from the left side of the PE can load in on the same clock cycle that the switch flag is set
    always_comb begin
        if (pe_switch_in) begin
            weight_reg_active = weight_reg_inactive;
        end
    end

    always_ff @(posedge clk or posedge rst) begin
        if (rst || !pe_enabled) begin
            pe_input_out <= 16'b0;
            weight_reg_active <= 16'b0;
            weight_reg_inactive <= 16'b0;
            pe_valid_out <= 0;
            pe_weight_out <= 16'b0;
            pe_switch_out <= 0;
        end else begin
            pe_valid_out <= pe_valid_in;
            pe_switch_out <= pe_switch_in;
            
            // Weight register updates - only on clock edges
            if (pe_accept_w_in) begin
                weight_reg_inactive <= pe_weight_in;
                pe_weight_out <= pe_weight_in;
            end else begin
                pe_weight_out <= 0;
            end

            if (pe_valid_in) begin
                pe_input_out <= pe_input_in;
                pe_psum_out <= mac_out;
            end else begin
                pe_valid_out <= 0;
                pe_psum_out <= 16'b0;
            end

        end
    end

endmodule
// -------- merged from bias_child.sv --------

module bias_child (
    input wire logic clk,
    input wire logic rst,

    input wire logic signed [15:0] bias_scalar_in, // bias scalars fetched from the unified buffer (rename it to bias_scalar_ub_in)
    output var logic bias_Z_valid_out, 
    input wire signed [15:0] bias_sys_data_in, // data from systolic array
    input wire bias_sys_valid_in, // valid signal from the systolic array

    output var logic signed [15:0] bias_z_data_out
);
    // output of the bias operation
    logic signed [15:0] z_pre_activation; 

    fxp_add add_inst(
        .ina(bias_sys_data_in),
        .inb(bias_scalar_in),
        .out(z_pre_activation)
    );
    // TODO: we only switch bias values for EACH layer!!!! maybe change logic herer

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            bias_Z_valid_out <= 1'b0; // reset the output valid signal
            bias_z_data_out <= 16'b0; // reset the output data
        end else begin
            if (bias_sys_valid_in) begin // valid data coming through
                bias_Z_valid_out <= 1'b1;
                bias_z_data_out <= z_pre_activation; // output of the bias operation
            end else begin
                bias_Z_valid_out <= 1'b0; // output is invalid otherwise
                bias_z_data_out <= 16'b0; // reset the output data
            end
        end
    end

endmodule
// -------- merged from bias_parent.sv --------

module bias_parent(
    input wire logic clk,
    input wire logic rst,

    input wire logic signed [15:0] bias_scalar_in_1,
    input wire logic signed [15:0] bias_scalar_in_2, // bias scalars fetched from the unified buffer (rename it to bias_scalar_ub_in)

    output var logic bias_Z_valid_out_1,
    output var logic bias_Z_valid_out_2,

    input wire signed [15:0] bias_sys_data_in_1,
    input wire signed [15:0] bias_sys_data_in_2,

    input wire bias_sys_valid_in_1,
    input wire bias_sys_valid_in_2,

    output var logic signed [15:0] bias_z_data_out_1,
    output var logic signed [15:0] bias_z_data_out_2

); 
    // Each bias module handles a feature column for a pre-activation matrix. 

    bias_child column_1 (
        .clk(clk),
        .rst(rst),
        .bias_scalar_in(bias_scalar_in_1),
        .bias_Z_valid_out(bias_Z_valid_out_1),
        .bias_sys_data_in(bias_sys_data_in_1),
        .bias_sys_valid_in(bias_sys_valid_in_1),
        .bias_z_data_out(bias_z_data_out_1)
    );

    bias_child column_2 (
        .clk(clk),
        .rst(rst),
        .bias_scalar_in(bias_scalar_in_2),
        .bias_Z_valid_out(bias_Z_valid_out_2),
        .bias_sys_data_in(bias_sys_data_in_2),
        .bias_sys_valid_in(bias_sys_valid_in_2),
        .bias_z_data_out(bias_z_data_out_2)
    );


endmodule
// -------- merged from control_unit.sv --------

module control_unit (
    input logic [87:0] instruction,  // updated to 88 bits total (0-87)
    
    // 1-bit signals - 5
    output logic sys_switch_in,
    output logic ub_rd_start_in,
    output logic ub_rd_transpose,
    output logic ub_wr_host_valid_in_1,
    output logic ub_wr_host_valid_in_2,
    
    // 2 bit signals
    output logic [1:0] ub_rd_col_size,

    // 8-bit signals
    output logic [7:0] ub_rd_row_size,
    output logic [1:0] ub_rd_addr_in,

    // 3 bit signals
    output logic [2:0] ub_ptr_sel,

    //16 bit signals
    output logic [15:0] ub_wr_host_data_in_1,
    output logic [15:0] ub_wr_host_data_in_2,

    // 4-bit signal
    output logic [3:0] vpu_data_pathway,

    //16-bit signals
    output logic [15:0] inv_batch_size_times_two_in,
    output logic [15:0] vpu_leak_factor_in
);

    // continuous assignments mapping instruction bits to output signals in sequential order
    // bits 0-4: 1-bit signals (5 bits total)
    assign sys_switch_in = instruction[0];
    assign ub_rd_start_in = instruction[1];
    assign ub_rd_transpose = instruction[2];
    assign ub_wr_host_valid_in_1 = instruction[3];
    assign ub_wr_host_valid_in_2 = instruction[4];
    
    // bits 5-6: 2-bit signal
    assign ub_rd_col_size = instruction[6:5];
    
    // bits 7-14: 8-bit signal
    assign ub_rd_row_size = instruction[14:7];
    
    // bits 15-16: 2-bit signal
    assign ub_rd_addr_in = instruction[16:15];
    
    // bits 17-19: 3-bit signal
    assign ub_ptr_sel = instruction[19:17];
    
    // bits 20-35: 16-bit signal
    assign ub_wr_host_data_in_1 = instruction[35:20];
    
    // bits 36-51: 16-bit signal
    assign ub_wr_host_data_in_2 = instruction[51:36];
    
    // bits 52-55: 4-bit signal
    assign vpu_data_pathway = instruction[55:52];
    
    // bits 56-71: 16-bit signal
    assign inv_batch_size_times_two_in = instruction[71:56];
    
    // bits 72-87: 16-bit signal
    assign vpu_leak_factor_in = instruction[87:72];

endmodule
// -------- merged from gradient_descent.sv --------

module gradient_descent (
    input logic clk,
    input logic rst,

    // learning rate
    input logic [15:0] lr_in,

    // old weight
    input logic [15:0] value_old_in,

    // gradient
    input logic [15:0] grad_in,

    // start signal
    input logic grad_descent_valid_in,

    // bias or weight
    input logic grad_bias_or_weight,

    // updated weight and done signal
    output logic [15:0] value_updated_out,
    output logic grad_descent_done_out
);

    logic [15:0] sub_value_out;
    logic grad_descent_in_reg;
    logic [15:0] sub_in_a;
    logic [15:0] mul_out;

    fxp_mul mul_inst (
        .ina(grad_in),
        .inb(lr_in),
        .out(mul_out),
        .overflow()
    );

    fxp_addsub sub_inst (
        .ina(sub_in_a),
        .inb(mul_out),
        .sub(1'b1),
        .out(sub_value_out),
        .overflow()
    );

    always_comb begin
        case(grad_bias_or_weight)
            1'b0: begin
                if(grad_descent_done_out) begin
                    sub_in_a = value_updated_out;
                end else begin
                    sub_in_a = value_old_in;
                end
            end

            1'b1: begin
                sub_in_a = value_old_in;
            end
        endcase
    end

    always_ff @(posedge clk or posedge rst) begin
        if(rst) begin
            sub_in_a <= '0;
            value_updated_out <= '0;
            grad_descent_done_out <= '0;
        end else begin
            grad_descent_done_out <= grad_descent_valid_in;
            if(grad_descent_valid_in) begin
                value_updated_out <= sub_value_out;
            end else begin
                value_updated_out <= '0;
            end
        end
    end


endmodule
// -------- merged from leaky_relu_child.sv --------

module leaky_relu_child (
    input wire logic clk,
    input wire logic rst,
    input wire logic lr_valid_in,
    input wire logic signed [15:0] lr_data_in,
    input wire logic signed [15:0] lr_leak_factor_in,
    output var logic signed [15:0] lr_data_out,
    output var logic lr_valid_out
);

    // fixed point module and storage
    logic signed [15:0] mul_out;
    fxp_mul mul_inst(
        .ina(lr_data_in),
        .inb(lr_leak_factor_in),
        .out(mul_out)
    );


    always @(posedge clk or posedge rst) begin
        if (rst) begin
            lr_data_out <= 16'b0;
            lr_valid_out <= 0;
        end else begin
            // valid date coming through
            if (lr_valid_in) begin
                if (lr_data_in >= 0) begin // if positive, then pass through 
                    lr_data_out <= lr_data_in; 
                end 
                else begin  // if negative,
                    lr_data_out <= mul_out;
                end
                lr_valid_out <= 1;
            end else begin
                lr_valid_out <= 0;
                lr_data_out <= 16'b0;
            end
        end
    end

endmodule
// -------- merged from leaky_relu_derivative_child.sv --------

module leaky_relu_derivative_child(
    input wire logic clk,
    input wire logic rst,

    input wire logic lr_d_valid_in,
    input wire logic signed [15:0] lr_d_data_in,
    input wire logic signed [15:0] lr_leak_factor_in,
    input wire logic signed [15:0] lr_d_H_data_in, // H data coming through

    output var logic lr_d_valid_out,
    output var logic signed [15:0] lr_d_data_out
);
    // fixed point module and storage
    logic signed [15:0] mul_out;
    fxp_mul mul_inst(
        .ina(lr_d_data_in),
        .inb(lr_leak_factor_in),
        .out(mul_out)
    );

    always @(posedge clk or posedge rst) begin
        if (rst) begin
            lr_d_data_out <= 16'b0;
            lr_d_valid_out <= 0;
        end else begin
            lr_d_valid_out <= lr_d_valid_in;
            if (lr_d_valid_in) begin
                if (lr_d_H_data_in >= 0) begin      // if derivative is positive, then pass through 
                    lr_d_data_out <= lr_d_data_in; 
                end else begin                  // if negative,
                    lr_d_data_out <= mul_out;
                end
            end else begin
                lr_d_data_out <= 16'b0;
            end
        end
    end


endmodule
// -------- merged from leaky_relu_derivative_parent.sv --------

module leaky_relu_derivative_parent (
    input wire logic clk,
    input wire logic rst,
    input wire logic signed [15:0] lr_leak_factor_in,

    input wire logic lr_d_valid_1_in,
    input wire logic lr_d_valid_2_in,

    input wire logic signed [15:0] lr_d_data_1_in,
    input wire logic signed [15:0] lr_d_data_2_in,

    input wire logic signed [15:0] lr_d_H_1_in,
    input wire logic signed [15:0] lr_d_H_2_in,
    
    output var logic signed [15:0] lr_d_data_1_out,
    output var logic signed [15:0] lr_d_data_2_out,
    
    output var logic lr_d_valid_1_out,
    output var logic lr_d_valid_2_out
);

    leaky_relu_derivative_child lr_d_col_1 (
        .clk(clk),
        .rst(rst),
        .lr_d_valid_in(lr_d_valid_1_in),
        .lr_d_data_in(lr_d_data_1_in),
        .lr_leak_factor_in(lr_leak_factor_in),
        .lr_d_data_out(lr_d_data_1_out),
        .lr_d_valid_out(lr_d_valid_1_out),
        .lr_d_H_data_in(lr_d_H_1_in) // H data for col 1 
    );

    leaky_relu_derivative_child lr_d_col_2 (
        .clk(clk),
        .rst(rst),
        .lr_d_valid_in(lr_d_valid_2_in),
        .lr_d_data_in(lr_d_data_2_in),
        .lr_leak_factor_in(lr_leak_factor_in),
        .lr_d_data_out(lr_d_data_2_out),
        .lr_d_valid_out(lr_d_valid_2_out),
        .lr_d_H_data_in(lr_d_H_2_in) // H data for col 2
    );

endmodule
// -------- merged from leaky_relu_parent.sv --------

module leaky_relu_parent (
    input wire logic clk,
    input wire logic rst,
    input wire logic signed [15:0] lr_leak_factor_in,

    input wire logic lr_valid_1_in,
    input wire logic lr_valid_2_in,

    input wire logic signed [15:0] lr_data_1_in,
    input wire logic signed [15:0] lr_data_2_in,
    
    output var logic signed [15:0] lr_data_1_out,
    output var logic signed [15:0] lr_data_2_out,
    
    output var logic lr_valid_1_out,
    output var logic lr_valid_2_out
);

    leaky_relu_child leaky_relu_col_1 (
        .clk(clk),
        .rst(rst),
        .lr_valid_in(lr_valid_1_in),
        .lr_data_in(lr_data_1_in),
        .lr_leak_factor_in(lr_leak_factor_in),
        .lr_data_out(lr_data_1_out),
        .lr_valid_out(lr_valid_1_out)
    );

    leaky_relu_child leaky_relu_col_2 (
        .clk(clk),
        .rst(rst),
        .lr_valid_in(lr_valid_2_in),
        .lr_data_in(lr_data_2_in),
        .lr_leak_factor_in(lr_leak_factor_in),
        .lr_data_out(lr_data_2_out),
        .lr_valid_out(lr_valid_2_out)
    );

endmodule
// -------- merged from loss_child.sv --------
`default_nettype none

// child loss module for MSE backward pass (gradient computation)
module loss_child (
    input wire logic clk,
    input wire logic rst,
    
    input wire logic signed [15:0] H_in,
    input wire logic signed [15:0] Y_in,
    input wire logic valid_in,
    input wire logic signed [15:0] inv_batch_size_times_two_in,  // 2/N as fixed-point input
    
    output var logic signed [15:0] gradient_out,
    output var logic valid_out
);
    
    // pipeline stages for MSE backward pass: (2/N) * (H - Y)
    logic signed [15:0] diff_stage1;
    logic signed [15:0] final_gradient;
    

    // stage 1 - compute difference (H - Y)
    fxp_addsub subtractor (
        .ina(H_in),
        .inb(Y_in),
        .sub(1'b1), // Subtraction
        .out(diff_stage1),
        .overflow()
    );
    
    // stage 2 - multiply by 2/N
    fxp_mul multiplier (
        .ina(diff_stage1),
        .inb(inv_batch_size_times_two_in),
        .out(final_gradient),
        .overflow()
    );
    
    // pipeline valid signals
    always_ff @(posedge clk or posedge rst) begin
        if (rst) begin
            gradient_out <= '0;
            valid_out <= '0;
        end else begin
            valid_out <= valid_in;
            gradient_out <= final_gradient;
        end
    end

endmodule



// -------- merged from loss_parent.sv --------

module loss_parent (
    input wire logic clk,
    input wire logic rst,
    
    input wire logic signed [15:0] H_1_in,
    input wire logic signed [15:0] Y_1_in,
    input wire logic signed [15:0] H_2_in,
    input wire logic signed [15:0] Y_2_in,
    
    input wire logic valid_1_in,
    input wire logic valid_2_in,
    
    input wire logic signed [15:0] inv_batch_size_times_two_in,  // 2/N as fixed-point input
    output var logic signed [15:0] gradient_1_out,
    output var logic signed [15:0] gradient_2_out,
    output var logic valid_1_out,
    output var logic valid_2_out
);

// loss child #1 instantiation
loss_child first_column (
    .clk(clk),
    .rst(rst),
    .H_in(H_1_in),
    .Y_in(Y_1_in),
    .valid_in(valid_1_in),
    .inv_batch_size_times_two_in(inv_batch_size_times_two_in),
    .gradient_out(gradient_1_out), 
    .valid_out(valid_1_out)
);

// loss child #2 instantiation
loss_child second_column (
    .clk(clk),
    .rst(rst),
    .H_in(H_2_in),
    .Y_in(Y_2_in),
    .valid_in(valid_2_in),
    .inv_batch_size_times_two_in(inv_batch_size_times_two_in),
    .gradient_out(gradient_2_out),
    .valid_out(valid_2_out)
);


endmodule
// -------- merged from systolic.sv --------

// 2x2 systolic array
module systolic #(
    parameter int SYSTOLIC_ARRAY_WIDTH = 2
)(
    input logic clk,
    input logic rst,

    // input signals from left side of systolic array
    input logic [15:0] sys_data_in_11,
    input logic [15:0] sys_data_in_21,
    input logic sys_start,    // start signal

    output logic [15:0] sys_data_out_21,
    output logic [15:0] sys_data_out_22,
    output wire sys_valid_out_21, 
    output wire sys_valid_out_22,

    // input signals from top of systolic array
    input logic [15:0] sys_weight_in_11, 
    input logic [15:0] sys_weight_in_12,
    input logic sys_accept_w_1,             // accept weight signal propagates only from top to bottom in column 1
    input logic sys_accept_w_2,             // accept weight signal propagates only from top to bottom in column 2

    input logic sys_switch_in,               // switch signal copies weight from shadow buffer to active buffer. propagates from top left to bottom right

    input logic [15:0] ub_rd_col_size_in,
    input logic ub_rd_col_size_valid_in
);

    // input_out for each PE (left to right)
    logic [15:0] pe_input_out_11;
    logic [15:0] pe_input_out_21;

    // psum_out for each PE (top to bottom)
    logic [15:0] pe_psum_out_11;
    logic [15:0] pe_psum_out_12;

    // weight_out for each PE (top to bottom)
    logic [15:0] pe_weight_out_11;
    logic [15:0] pe_weight_out_12;

    // switch_out for each PE
    logic pe_switch_out_11;
    logic pe_switch_out_12;
    
    // valid_out for each PE (top to bottom)
    wire pe_valid_out_11;   // this wire will connect the valid signal from pe11 to pe12
    wire pe_valid_out_12;   // this wire will connect the valid signal from pe21 to pe22

    // PE columns to enable
    logic [1:0] pe_enabled;

    pe pe11 (
        .clk(clk),
        .rst(rst),
        .pe_enabled(pe_enabled[0]),

        .pe_valid_in(sys_start),
        .pe_valid_out(pe_valid_out_11), // valid out signal is now dispatched onto pe_valid_out_11

        .pe_accept_w_in(sys_accept_w_1),
        .pe_switch_in(sys_switch_in),
        .pe_switch_out(pe_switch_out_11),

        .pe_input_in(sys_data_in_11),
        .pe_psum_in(16'b0),
        .pe_weight_in(sys_weight_in_11),
        .pe_input_out(pe_input_out_11),
        .pe_psum_out(pe_psum_out_11),
        .pe_weight_out(pe_weight_out_11)
    );

    pe pe12 (
        .clk(clk),
        .rst(rst),
        .pe_enabled(pe_enabled[1]),

        .pe_valid_in(pe_valid_out_11),
        .pe_valid_out(pe_valid_out_12),

        .pe_accept_w_in(sys_accept_w_2),
        .pe_switch_in(pe_switch_out_11),
        .pe_switch_out(pe_switch_out_12),

        .pe_input_in(pe_input_out_11),
        .pe_psum_in(16'b0),
        .pe_weight_in(sys_weight_in_12),
        .pe_input_out(),
        .pe_psum_out(pe_psum_out_12),
        .pe_weight_out(pe_weight_out_12)
    );

    pe pe21 (
        .clk(clk),
        .rst(rst),
        .pe_enabled(pe_enabled[0]),

        .pe_valid_in(pe_valid_out_11),
        .pe_valid_out(sys_valid_out_21),

        .pe_accept_w_in(sys_accept_w_1),
        .pe_switch_in(pe_switch_out_11),
        .pe_switch_out(),

        .pe_input_in(sys_data_in_21),
        .pe_psum_in(pe_psum_out_11),
        .pe_weight_in(pe_weight_out_11),
        .pe_input_out(pe_input_out_21),
        .pe_psum_out(sys_data_out_21),
        .pe_weight_out()
    );

    pe pe22 ( // connect this to pe_valid out of pe 21? 
        .clk(clk),
        .rst(rst),
        .pe_enabled(pe_enabled[1]),

        .pe_valid_in(pe_valid_out_12),
        .pe_valid_out(sys_valid_out_22),

        .pe_accept_w_in(sys_accept_w_2),
        .pe_switch_in(pe_switch_out_12),
        .pe_switch_out(),

        .pe_input_in(pe_input_out_21),
        .pe_psum_in(pe_psum_out_12),
        .pe_weight_in(pe_weight_out_12),
        .pe_input_out(),
        .pe_psum_out(sys_data_out_22),
        .pe_weight_out()
    );

    always@(posedge clk or posedge rst) begin
        if(rst) begin
            pe_enabled <= '0;
        end else begin
            if(ub_rd_col_size_valid_in) begin
                pe_enabled <= (1 << ub_rd_col_size_in) - 1;
            end
        end
    end

endmodule
// -------- merged from unified_buffer.sv --------
`timescale 1ns/1ps
`default_nettype none

module unified_buffer #(
    parameter int UNIFIED_BUFFER_WIDTH = 128,
    parameter int SYSTOLIC_ARRAY_WIDTH = 2
)(
    input logic clk,
    input logic rst,

    // Write ports from VPU to UB
    input logic [15:0] ub_wr_data_in [SYSTOLIC_ARRAY_WIDTH],
    input logic ub_wr_valid_in [SYSTOLIC_ARRAY_WIDTH],

    // Write ports from host to UB (for loading in parameters)
    input logic [15:0] ub_wr_host_data_in [SYSTOLIC_ARRAY_WIDTH],
    input logic ub_wr_host_valid_in [SYSTOLIC_ARRAY_WIDTH],

    // Read instruction input from instruction memory
    input logic ub_rd_start_in,
    input logic ub_rd_transpose,
    input logic [8:0] ub_ptr_select,
    input logic [15:0] ub_rd_addr_in,
    input logic [15:0] ub_rd_row_size,
    input logic [15:0] ub_rd_col_size,

    // Learning rate input
    input logic [15:0] learning_rate_in,

    // Read ports from UB to left side of systolic array
    // (I had trouble connecting arrays of ports to other modules in the tpu.sv file for some reason so I had to split them like so)
    output logic [15:0] ub_rd_input_data_out_0,
    output logic [15:0] ub_rd_input_data_out_1,
    output logic ub_rd_input_valid_out_0,
    output logic ub_rd_input_valid_out_1,

    // Read ports from UB to top of systolic array
    output logic [15:0] ub_rd_weight_data_out_0,
    output logic [15:0] ub_rd_weight_data_out_1,
    output logic ub_rd_weight_valid_out_0,
    output logic ub_rd_weight_valid_out_1,

    // Read ports from UB to bias modules in VPU
    output logic [15:0] ub_rd_bias_data_out_0,
    output logic [15:0] ub_rd_bias_data_out_1,

    // Read ports from UB to loss modules (Y matrices) in VPU
    output logic [15:0] ub_rd_Y_data_out_0,
    output logic [15:0] ub_rd_Y_data_out_1,

    // Read ports from UB to activation derivative modules (H matrices) in VPU
    output logic [15:0] ub_rd_H_data_out_0,
    output logic [15:0] ub_rd_H_data_out_1,

    // Outputs to send number of columns to systolic array
    output logic [15:0] ub_rd_col_size_out,
    output logic ub_rd_col_size_valid_out
);

    logic [15:0] ub_memory [0:UNIFIED_BUFFER_WIDTH-1];

    logic [15:0] ub_rd_input_data_out [SYSTOLIC_ARRAY_WIDTH];
    logic ub_rd_input_valid_out [SYSTOLIC_ARRAY_WIDTH];
    logic [15:0] ub_rd_weight_data_out [SYSTOLIC_ARRAY_WIDTH];
    logic ub_rd_weight_valid_out [SYSTOLIC_ARRAY_WIDTH];
    logic [15:0] ub_rd_bias_data_out [SYSTOLIC_ARRAY_WIDTH];
    logic [15:0] ub_rd_Y_data_out [SYSTOLIC_ARRAY_WIDTH];
    logic [15:0] ub_rd_H_data_out [SYSTOLIC_ARRAY_WIDTH];

    logic [15:0] wr_ptr;

    // Internal logic for reading inputs from UB to left side of systolic array
    logic [15:0] rd_input_ptr;
    logic [15:0] rd_input_row_size;
    logic [15:0] rd_input_col_size;
    logic [15:0] rd_input_time_counter;
    logic rd_input_transpose;

    // Internal logic for reading weights from UB to left side of systolic array
    logic signed [15:0] rd_weight_ptr;
    logic [15:0] rd_weight_row_size;
    logic [15:0] rd_weight_col_size;
    logic [15:0] rd_weight_time_counter;
    logic rd_weight_transpose;
    logic [15:0] rd_weight_skip_size;

    // Internal logic for bias inputs from UB to bias modules in VPU
    logic [15:0] rd_bias_ptr;
    logic [15:0] rd_bias_row_size;
    logic [15:0] rd_bias_col_size;
    logic [15:0] rd_bias_time_counter;

    // Internal logic for Y inputs from UB to loss modules in VPU
    logic [15:0] rd_Y_ptr;
    logic [15:0] rd_Y_row_size;
    logic [15:0] rd_Y_col_size;
    logic [15:0] rd_Y_time_counter;

    // Internal logic for bias inputs from UB to activation derivative modules in VPU
    logic [15:0] rd_H_ptr;
    logic [15:0] rd_H_row_size;
    logic [15:0] rd_H_col_size;
    logic [15:0] rd_H_time_counter; 

    // Internal logic for bias gradient descent inputs from UB to gradient descent modules
    logic [15:0] rd_grad_bias_ptr;
    logic [15:0] rd_grad_bias_row_size;
    logic [15:0] rd_grad_bias_col_size;
    logic [15:0] rd_grad_bias_time_counter; 

    // Internal logic for weight gradient descent inputs from UB to gradient descent modules
    logic [15:0] rd_grad_weight_ptr;
    logic [15:0] rd_grad_weight_row_size;
    logic [15:0] rd_grad_weight_col_size;
    logic [15:0] rd_grad_weight_time_counter; 

    // Internal logic for gradient descent inputs from UB to gradient descent modules
    logic [15:0] value_old_in [SYSTOLIC_ARRAY_WIDTH];
    logic grad_descent_valid_in [SYSTOLIC_ARRAY_WIDTH];
    logic [15:0] value_updated_out [SYSTOLIC_ARRAY_WIDTH];
    logic grad_descent_done_out [SYSTOLIC_ARRAY_WIDTH];
    
    // Where to write gradients to UB
    logic [15:0] grad_descent_ptr;

    // Whether the gradients are biases or weights (0 for biases, 1 for weights)
    logic grad_bias_or_weight;

    genvar i;
    generate
        for (i=0; i<SYSTOLIC_ARRAY_WIDTH; i++) begin : gradient_descent_gen
            gradient_descent gradient_descent_inst (
                .clk(clk),
                .rst(rst),
                .lr_in(learning_rate_in),
                .grad_in(ub_wr_data_in[i]),
                .value_old_in(value_old_in[i]),
                .grad_descent_valid_in(grad_descent_valid_in[i]),
                .grad_bias_or_weight(grad_bias_or_weight),
                .value_updated_out(value_updated_out[i]),
                .grad_descent_done_out(grad_descent_done_out[i])
            );
        end
    endgenerate

    // (I had trouble connecting arrays of ports to other modules in the tpu.sv file for some reason, so I had to connect them to split up output ports like so)
    assign ub_rd_input_data_out_0 = ub_rd_input_data_out[0];
    assign ub_rd_input_data_out_1 = ub_rd_input_data_out[1];
    assign ub_rd_input_valid_out_0 = ub_rd_input_valid_out[0];
    assign ub_rd_input_valid_out_1 = ub_rd_input_valid_out[1];

    assign ub_rd_weight_data_out_0 = ub_rd_weight_data_out[0];
    assign ub_rd_weight_data_out_1 = ub_rd_weight_data_out[1];
    assign ub_rd_weight_valid_out_0 = ub_rd_weight_valid_out[0];
    assign ub_rd_weight_valid_out_1 = ub_rd_weight_valid_out[1];

    assign ub_rd_bias_data_out_0 = ub_rd_bias_data_out[0];
    assign ub_rd_bias_data_out_1 = ub_rd_bias_data_out[1];

    assign ub_rd_Y_data_out_0 = ub_rd_Y_data_out[0];
    assign ub_rd_Y_data_out_1 = ub_rd_Y_data_out[1];

    assign ub_rd_H_data_out_0 = ub_rd_H_data_out[0];
    assign ub_rd_H_data_out_1 = ub_rd_H_data_out[1];

    always_comb begin
        //READING LOGIC (UB to left side of systolic array)
        if (ub_rd_start_in) begin
            case (ub_ptr_select)
                0: begin
                    rd_input_transpose = ub_rd_transpose;
                    rd_input_ptr = ub_rd_addr_in;

                    if(ub_rd_transpose) begin   // Switch columns and rows!
                        rd_input_row_size = ub_rd_col_size;
                        rd_input_col_size = ub_rd_row_size;
                    end else begin
                        rd_input_row_size = ub_rd_row_size;
                        rd_input_col_size = ub_rd_col_size;
                    end

                    rd_input_time_counter = '0;
                end
                1: begin
                    rd_weight_transpose = ub_rd_transpose;

                    if(ub_rd_transpose) begin   // Switch columns and rows!
                        rd_weight_row_size = ub_rd_col_size;
                        rd_weight_col_size = ub_rd_row_size;
                        rd_weight_ptr = ub_rd_addr_in + ub_rd_col_size - 1;
                        ub_rd_col_size_out = ub_rd_row_size;
                    end else begin
                        rd_weight_row_size = ub_rd_row_size;
                        rd_weight_col_size = ub_rd_col_size;
                        rd_weight_ptr = ub_rd_addr_in + ub_rd_row_size*ub_rd_col_size - ub_rd_col_size;
                        ub_rd_col_size_out = ub_rd_col_size;
                    end

                    rd_weight_skip_size = ub_rd_col_size + 1;
                    rd_weight_time_counter = '0;
                    ub_rd_col_size_valid_out = 1'b1;
                end
                2: begin
                    rd_bias_ptr = ub_rd_addr_in;
                    rd_bias_row_size = ub_rd_row_size;
                    rd_bias_col_size = ub_rd_col_size;
                    rd_bias_time_counter = '0;
                end
                3: begin
                    rd_Y_ptr = ub_rd_addr_in;
                    rd_Y_row_size = ub_rd_row_size;
                    rd_Y_col_size = ub_rd_col_size;
                    rd_Y_time_counter = '0;
                end
                4: begin
                    rd_H_ptr = ub_rd_addr_in;
                    rd_H_row_size = ub_rd_row_size;
                    rd_H_col_size = ub_rd_col_size;
                    rd_H_time_counter = '0;
                end
                5: begin
                    rd_grad_bias_ptr = ub_rd_addr_in;
                    rd_grad_bias_row_size = ub_rd_row_size;
                    rd_grad_bias_col_size = ub_rd_col_size;
                    rd_grad_bias_time_counter = '0;
                    grad_bias_or_weight = 1'b0;
                    grad_descent_ptr = ub_rd_addr_in;
                end
                6: begin
                    rd_grad_weight_ptr = ub_rd_addr_in;
                    rd_grad_weight_row_size = ub_rd_row_size;
                    rd_grad_weight_col_size = ub_rd_col_size;
                    rd_grad_weight_time_counter = '0;
                    grad_bias_or_weight = 1'b1;
                    grad_descent_ptr = ub_rd_addr_in;
                end
            endcase
        end else begin
            ub_rd_col_size_out = 0;
            ub_rd_col_size_valid_out = 1'b0;
        end
    end

    always_comb begin   // Automatically turn on gradient descent modules when bias or weight gradient descent pointers have been set by a read command
        if (
            rd_grad_bias_time_counter < rd_grad_bias_row_size + rd_grad_bias_col_size ||
            rd_grad_weight_time_counter < rd_grad_weight_row_size + rd_grad_weight_col_size
        ) begin
            for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                grad_descent_valid_in[i] = ub_wr_valid_in[i];
            end
        end else begin
            for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                grad_descent_valid_in[i] = 1'b0;
            end
        end
    end 

    always @(posedge clk or posedge rst) begin
        // Display variables in GTKWave
        for (int i = 0; i < UNIFIED_BUFFER_WIDTH; i++) begin
            $dumpvars(0, ub_memory[i]);
        end
        for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
            $dumpvars(0, ub_wr_data_in[i]);
            $dumpvars(0, ub_wr_valid_in[i]);
            $dumpvars(0, ub_rd_input_data_out[i]);
            $dumpvars(0, ub_rd_input_valid_out[i]);
            $dumpvars(0, ub_rd_weight_data_out[i]);
            $dumpvars(0, ub_rd_weight_valid_out[i]);
            $dumpvars(0, ub_rd_bias_data_out[i]);
            $dumpvars(0, ub_rd_Y_data_out[i]);
            $dumpvars(0, ub_rd_H_data_out[i]);
            $dumpvars(0, value_old_in[i]);
            $dumpvars(0, grad_descent_valid_in[i]);
            $dumpvars(0, grad_descent_done_out[i]);
            $dumpvars(0, value_updated_out[i]);
        end


        if (rst) begin
            // reset all memory to 0
            for (int i = 0; i < UNIFIED_BUFFER_WIDTH; i++) begin
                ub_memory[i] <= '0;
            end

            // set internal registers to 0
            for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                ub_rd_input_data_out[i] <= '0;
                ub_rd_input_valid_out[i] <= '0;
                ub_rd_weight_data_out[i] <= '0;
                ub_rd_weight_valid_out[i] <= '0;
                ub_rd_bias_data_out[i] <= '0;
                ub_rd_Y_data_out[i] <= '0;
                ub_rd_H_data_out[i] <= '0;
                value_old_in[i] <= '0;
                grad_descent_valid_in[i] <= '0;
            end

            wr_ptr <= '0;

            rd_input_ptr <= '0;
            rd_input_row_size <= '0;
            rd_input_col_size <= '0;
            rd_input_time_counter <= '0;
            rd_input_transpose <= '0;

            rd_weight_ptr <= '0;
            rd_weight_row_size <= '0;
            rd_weight_col_size <= '0;
            rd_weight_time_counter <= '0;
            rd_weight_transpose <= '0;

            rd_bias_ptr <= '0;
            rd_bias_row_size <= '0;
            rd_bias_col_size <= '0;
            rd_bias_time_counter <= '0;

            rd_Y_ptr <= '0;
            rd_Y_row_size <= '0;
            rd_Y_col_size <= '0;
            rd_Y_time_counter <= '0;

            rd_H_ptr <= '0;
            rd_H_row_size <= '0;
            rd_H_col_size <= '0;
            rd_H_time_counter <= '0;

            rd_grad_bias_ptr <= '0;
            rd_grad_bias_row_size <= '0;
            rd_grad_bias_col_size <= '0;
            rd_grad_bias_time_counter <= '0;

            rd_grad_weight_ptr <= '0;
            rd_grad_weight_row_size <= '0;
            rd_grad_weight_col_size <= '0;
            rd_grad_weight_time_counter <= '0;
        end else begin
            // WRITING LOGIC
            // matrices are stored in row major format
            // if there are two columns, the first column will be stored at even indices and the second column will be stored at odd indices
            for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin     // FOR LOOP SHOULD DECREMENT TO STORE IN ROW MAJOR ORDER!!! yooooooooo
                if (ub_wr_valid_in[i]) begin
                    ub_memory[wr_ptr] <= ub_wr_data_in[i];
                    wr_ptr = wr_ptr + 1;                                // I should get rid of this (not good to mix non blocking and blocking assignments) but it works for now
                end else if (ub_wr_host_valid_in[i]) begin
                    ub_memory[wr_ptr] <= ub_wr_host_data_in[i];
                    wr_ptr = wr_ptr + 1;
                end
            end

            //WRITING LOGIC (for gradient descent modules to UB)
            if (grad_bias_or_weight) begin
                for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
                    if (grad_descent_done_out[i]) begin
                        ub_memory[grad_descent_ptr] <= value_updated_out[i];
                        grad_descent_ptr = grad_descent_ptr + 1;
                    end
                end
            end else begin
                for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
                    if (grad_descent_done_out[i]) begin
                        ub_memory[grad_descent_ptr + i] <= value_updated_out[i];
                    end
                end
            end

            // READING LOGIC (for input from UB to left side of systolic array)
            if (rd_input_time_counter + 1 < rd_input_row_size + rd_input_col_size) begin
                if(rd_input_transpose) begin
                    // For transposed matrices (for loop should increment)
                    for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                        if(rd_input_time_counter >= i && rd_input_time_counter < rd_input_row_size + i && i < rd_input_col_size) begin 
                            ub_rd_input_valid_out[i] <= 1'b1;
                            ub_rd_input_data_out[i] <= ub_memory[rd_input_ptr];
                            rd_input_ptr = rd_input_ptr + 1;            // I should get rid of this (not good to mix non blocking and blocking assignments) but it works for now
                        end else begin 
                            ub_rd_input_valid_out[i] <= 1'b0;
                            ub_rd_input_data_out[i] <= '0;
                        end
                    end
                end else begin
                    // For untransposed matrices (for loop should decrement)
                    for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
                        if(rd_input_time_counter >= i && rd_input_time_counter < rd_input_row_size + i && i < rd_input_col_size) begin 
                            ub_rd_input_valid_out[i] <= 1'b1;
                            ub_rd_input_data_out[i] <= ub_memory[rd_input_ptr];
                            rd_input_ptr = rd_input_ptr + 1;            // I should get rid of this (not good to mix non blocking and blocking assignments) but it works for now    
                        end else begin 
                            ub_rd_input_valid_out[i] <= 1'b0;
                            ub_rd_input_data_out[i] <= '0;
                        end
                    end
                end
                rd_input_time_counter <= rd_input_time_counter + 1;
            end else begin 
                rd_input_ptr <= 0;
                rd_input_row_size <= 0;
                rd_input_col_size <= 0;
                rd_input_time_counter <= '0;
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    ub_rd_input_valid_out[i] <= 1'b0;
                    ub_rd_input_data_out[i] <= '0;
                end
            end

            // READING LOGIC (for weights from UB to top of systolic array)
            if (rd_weight_time_counter + 1 < rd_weight_row_size + rd_weight_col_size) begin
                if(rd_weight_transpose) begin
                    // For transposed matrices (for loop should increment)
                    for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                        if(rd_weight_time_counter >= i && rd_weight_time_counter < rd_weight_row_size + i && i < rd_weight_col_size) begin
                            ub_rd_weight_valid_out[i] <= 1'b1;
                            ub_rd_weight_data_out[i] <= ub_memory[rd_weight_ptr];
                            rd_weight_ptr = rd_weight_ptr + rd_weight_skip_size;
                        end else begin
                            ub_rd_weight_valid_out[i] <= 0;
                            ub_rd_weight_data_out[i] <= '0;
                        end
                    end
                    rd_weight_ptr = rd_weight_ptr - rd_weight_skip_size - 1;
                end else begin
                    // For untransposed matrices (for loop should decrement)
                    for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
                        if(rd_weight_time_counter >= i && rd_weight_time_counter < rd_weight_row_size + i && i < rd_weight_col_size) begin
                            ub_rd_weight_valid_out[i] <= 1'b1;
                            ub_rd_weight_data_out[i] <= ub_memory[rd_weight_ptr];
                            rd_weight_ptr = rd_weight_ptr - rd_weight_skip_size;
                        end else begin
                            ub_rd_weight_valid_out[i] <= 0;
                            ub_rd_weight_data_out[i] <= '0;
                        end
                    end
                    rd_weight_ptr = rd_weight_ptr + rd_weight_skip_size + 1;
                end
                rd_weight_time_counter <= rd_weight_time_counter + 1;
            end else begin
                rd_weight_ptr <= 0;
                rd_weight_row_size <= 0;
                rd_weight_col_size <= 0;
                rd_weight_time_counter <= '0;
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    ub_rd_weight_valid_out[i] <= 0;
                    ub_rd_weight_data_out[i] <= '0;
                end
            end

            // READING LOGIC (for bias inputs from UB to bias modules in VPU)
            if (rd_bias_time_counter + 1 < rd_bias_row_size + rd_bias_col_size) begin
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    if(rd_bias_time_counter >= i && rd_bias_time_counter < rd_bias_row_size + i && i < rd_bias_col_size) begin
                        ub_rd_bias_data_out[i] <= ub_memory[rd_bias_ptr + i];
                    end else begin
                        ub_rd_bias_data_out[i] <= '0;
                    end
                end
                rd_bias_time_counter <= rd_bias_time_counter + 1;
            end else begin
                rd_bias_ptr <= 0;
                rd_bias_row_size <= 0;
                rd_bias_col_size <= 0;
                rd_bias_time_counter <= '0;
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    ub_rd_bias_data_out[i] <= '0;
                end
            end

            // READING LOGIC (for Y inputs from UB to loss modules in VPU)
            if (rd_Y_time_counter + 1 < rd_Y_row_size + rd_Y_col_size) begin
                for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
                    if(rd_Y_time_counter >= i && rd_Y_time_counter < rd_Y_row_size + i && i < rd_Y_col_size) begin
                        ub_rd_Y_data_out[i] <= ub_memory[rd_Y_ptr];
                        rd_Y_ptr = rd_Y_ptr + 1;
                    end else begin
                        ub_rd_Y_data_out[i] <= '0;
                    end
                end
                rd_Y_time_counter <= rd_Y_time_counter + 1;
            end else begin
                rd_Y_ptr <= 0;
                rd_Y_row_size <= 0;
                rd_Y_col_size <= 0;
                rd_Y_time_counter <= '0;
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    ub_rd_Y_data_out[i] <= '0;
                end
            end

            // READING LOGIC (for H inputs from UB to activation derivative modules in VPU)
            if (rd_H_time_counter + 1 < rd_H_row_size + rd_H_col_size) begin
                for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
                    if(rd_H_time_counter >= i && rd_H_time_counter < rd_H_row_size + i && i < rd_H_col_size) begin
                        ub_rd_H_data_out[i] <= ub_memory[rd_H_ptr];
                        rd_H_ptr = rd_H_ptr + 1;
                    end else begin
                        ub_rd_H_data_out[i] <= '0;
                    end
                end
                rd_H_time_counter <= rd_H_time_counter + 1;
            end else begin
                rd_H_ptr <= 0;
                rd_H_row_size <= 0;
                rd_H_col_size <= 0;
                rd_H_time_counter <= '0;
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    ub_rd_H_data_out[i] <= '0;
                end
            end

            // READING LOGIC (for bias and weight gradient descent inputs from UB to gradient descent modules)
            if (rd_grad_bias_time_counter + 1 < rd_grad_bias_row_size + rd_grad_bias_col_size) begin
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    if(rd_grad_bias_time_counter >= i && rd_grad_bias_time_counter < rd_grad_bias_row_size + i && i < rd_grad_bias_col_size) begin
                        value_old_in[i] <= ub_memory[rd_grad_bias_ptr + i];
                    end else begin
                        value_old_in[i] <= '0;
                    end
                end
                rd_grad_bias_time_counter <= rd_grad_bias_time_counter + 1;
            end else if (rd_grad_weight_time_counter + 1 < rd_grad_weight_row_size + rd_grad_weight_col_size) begin
                for (int i = SYSTOLIC_ARRAY_WIDTH-1; i >= 0; i--) begin
                    if(rd_grad_weight_time_counter >= i && rd_grad_weight_time_counter < rd_grad_weight_row_size + i && i < rd_grad_weight_col_size) begin 
                        value_old_in[i] <= ub_memory[rd_grad_weight_ptr];
                        rd_grad_weight_ptr = rd_grad_weight_ptr + 1;            // I should get rid of this (not good to mix non blocking and blocking assignments) but it works for now    
                    end else begin 
                        value_old_in[i] <= '0;
                    end
                end
                rd_grad_weight_time_counter <= rd_grad_weight_time_counter + 1;
            end else begin
                rd_grad_bias_ptr <= 0;
                rd_grad_bias_row_size <= 0;
                rd_grad_bias_col_size <= 0;
                rd_grad_bias_time_counter <= '0;
                rd_grad_weight_ptr <= 0;
                rd_grad_weight_row_size <= 0;
                rd_grad_weight_col_size <= 0;
                rd_grad_weight_time_counter <= '0;
                for (int i = 0; i < SYSTOLIC_ARRAY_WIDTH; i++) begin
                    value_old_in[i] <= '0;
                end
            end
        end
    end
endmodule
// -------- merged from vpu.sv --------

// three data pathways:
// (forward pass hidden layer computations) input from sys --> bias --> leaky relu --> output
// (transition) input from sys --> bias --> leaky relu --> loss --> leaky relu derivative --> output
// (backward pass) input from sys --> leaky relu derivative --> output
// during the transition pathway we need to store the H matrices that come out of the leaky relu modules AND pass them to the loss modules

/* 
|bias control bit| |lr control bit| |loss control bit| |lr_d control bit|

0000: activate no modules
1100: forward pass pathway (sys --> bias --> leaky relu --> output)
1111: transistion pathway (sys --> bias --> leaky relu --> loss --> leaky relu derivative --> output)
0001: backward pass pathway (sys --> leaky relu derivative --> output)
*/

module vpu (
    input wire logic clk,
    input wire logic rst,

    input wire logic [3:0] vpu_data_pathway, // 4-bits to signify which modules to route the inputs to (1 bit for each module)

    // Inputs from systolic array
    input wire logic signed [15:0] vpu_data_in_1,
    input wire logic signed [15:0] vpu_data_in_2,
    input wire logic vpu_valid_in_1,
    input wire logic vpu_valid_in_2,

    // Inputs from UB
    input wire logic signed [15:0] bias_scalar_in_1,             // For bias modules
    input wire logic signed [15:0] bias_scalar_in_2,             // For bias modules
    input wire logic signed [15:0] lr_leak_factor_in,            // For leaky relu modules
    input wire logic signed [15:0] Y_in_1,                       // For loss modules
    input wire logic signed [15:0] Y_in_2,                       // For loss modules
    input wire logic signed [15:0] inv_batch_size_times_two_in,  // For loss modules
    input wire logic signed [15:0] H_in_1,                       // For leaky relu derivative modules
    input wire logic signed [15:0] H_in_2,                       // For leaky relu derivative modules

    // Outputs to UB
    output var logic signed [15:0] vpu_data_out_1,
    output var logic signed [15:0] vpu_data_out_2,
    output var logic vpu_valid_out_1,
    output var logic vpu_valid_out_2
);

    // bias
    logic [15:0] bias_data_1_in; 
    logic bias_valid_1_in;
    logic [15:0] bias_data_2_in;
    logic bias_valid_2_in;
    logic [15:0] bias_z_data_out_1;
    logic bias_valid_1_out;
    logic [15:0] bias_z_data_out_2;
    logic bias_valid_2_out;

    // bias to lr intermediate values
    logic [15:0] b_to_lr_data_in_1;
    logic b_to_lr_valid_in_1;
    logic [15:0] b_to_lr_data_in_2;
    logic b_to_lr_valid_in_2;

    // lr
    logic [15:0] lr_data_1_in; 
    logic lr_valid_1_in;
    logic [15:0] lr_data_2_in;
    logic lr_valid_2_in;
    logic [15:0] lr_data_1_out;
    logic lr_valid_1_out;
    logic [15:0] lr_data_2_out;
    logic lr_valid_2_out;

    // lr to loss intermediate values
    logic [15:0] lr_to_loss_data_in_1;
    logic lr_to_loss_valid_in_1;
    logic [15:0] lr_to_loss_data_in_2;
    logic lr_to_loss_valid_in_2;

    // loss
    logic [15:0] loss_data_1_in; 
    logic loss_valid_1_in;
    logic [15:0] loss_data_2_in;
    logic loss_valid_2_in;
    logic [15:0] loss_data_1_out;
    logic loss_valid_1_out;
    logic [15:0] loss_data_2_out;
    logic loss_valid_2_out;

    // loss to lrd intermediate values
    logic [15:0] loss_to_lrd_data_in_1;
    logic loss_to_lrd_valid_in_1;
    logic [15:0] loss_to_lrd_data_in_2;
    logic loss_to_lrd_valid_in_2;

    // lr_d
    logic [15:0] lr_d_data_1_in; 
    logic lr_d_valid_1_in;
    logic [15:0] lr_d_data_2_in;
    logic lr_d_valid_2_in;
    logic [15:0] lr_d_data_1_out;
    logic lr_d_valid_1_out;
    logic [15:0] lr_d_data_2_out;
    logic lr_d_valid_2_out;
    logic [15:0] lr_d_H_in_1;
    logic [15:0] lr_d_H_in_2;
    

    // temp 'last H matrix' cache
    logic [15:0] last_H_data_1_in;
    logic [15:0] last_H_data_2_in;
    logic [15:0] last_H_data_1_out;
    logic [15:0] last_H_data_2_out;

    bias_parent bias_parent_inst (  
        .clk(clk),
        .rst(rst),
        .bias_sys_data_in_1(bias_data_1_in),    // input
        .bias_sys_data_in_2(bias_data_2_in),    // input
        .bias_sys_valid_in_1(bias_valid_1_in),  // input
        .bias_sys_valid_in_2(bias_valid_2_in),  // input

        .bias_scalar_in_1(bias_scalar_in_1),    // input from UB
        .bias_scalar_in_2(bias_scalar_in_2),    // input from UB 

        .bias_Z_valid_out_1(bias_valid_1_out),  // output
        .bias_Z_valid_out_2(bias_valid_2_out),  // output
        .bias_z_data_out_1(bias_z_data_out_1),  // output
        .bias_z_data_out_2(bias_z_data_out_2)   // output
    );


    leaky_relu_parent leaky_relu_parent_inst (
        .clk(clk),
        .rst(rst),

        .lr_data_1_in(lr_data_1_in),                // input
        .lr_data_2_in(lr_data_2_in),                // input
        .lr_valid_1_in(lr_valid_1_in),              // input
        .lr_valid_2_in(lr_valid_2_in),              // input

        .lr_leak_factor_in(lr_leak_factor_in),      // input from UB
        
        .lr_data_1_out(lr_data_1_out),              // output 
        .lr_data_2_out(lr_data_2_out),              // output
        .lr_valid_1_out(lr_valid_1_out),            // output
        .lr_valid_2_out(lr_valid_2_out)             // output
    );

    loss_parent loss_parent_inst ( // TODO: THIS SHOULD BE RENAMED TO LOSS DERIVATIVE MODULE. WE DONT HAVE A MODULE TO COMPUTE THE LOSS
        .clk(clk),
        .rst(rst),
        .H_1_in(loss_data_1_in),        // input
        .H_2_in(loss_data_2_in),        // input
        .valid_1_in(loss_valid_1_in),   // input
        .valid_2_in(loss_valid_2_in),   // input

        .Y_1_in(Y_in_1),                // input from UB
        .Y_2_in(Y_in_2),                // input from UB
        .inv_batch_size_times_two_in(inv_batch_size_times_two_in),

        .gradient_1_out(loss_data_1_out), // output
        .gradient_2_out(loss_data_2_out), // output
        .valid_1_out(loss_valid_1_out),
        .valid_2_out(loss_valid_2_out)
    );

    leaky_relu_derivative_parent leaky_relu_derivative_parent_inst (
        .clk(clk),
        .rst(rst),
        .lr_d_data_1_in(lr_d_data_1_in),    // input
        .lr_d_data_2_in(lr_d_data_2_in),    // input
        .lr_d_valid_1_in(lr_d_valid_1_in),  // input
        .lr_d_valid_2_in(lr_d_valid_2_in),  // input
         
         // TODO - change this variable from leaky relu parent for consistency
        .lr_d_H_1_in(lr_d_H_in_1),              // input from UB or temp 'last H matrix' cache
        .lr_d_H_2_in(lr_d_H_in_2),              // input from UB or temp 'last H matrix' cache
        .lr_leak_factor_in(lr_leak_factor_in),
        
        .lr_d_data_1_out(lr_d_data_1_out),      // output
        .lr_d_data_2_out(lr_d_data_2_out),      // output
        .lr_d_valid_1_out(lr_d_valid_1_out),    // output
        .lr_d_valid_2_out(lr_d_valid_2_out)     // output
    );

    always @(*) begin
        if (rst) begin
            vpu_data_out_1 = 16'b0;
            vpu_data_out_2 = 16'b0;
            vpu_valid_out_1 = 1'b0;
            vpu_valid_out_2 = 1'b0;
            
            // default internal wire assignments during reset
            bias_data_1_in = 16'b0;
            bias_data_2_in = 16'b0;
            bias_valid_1_in = 1'b0;
            bias_valid_2_in = 1'b0;
            lr_data_1_in = 16'b0;
            lr_data_2_in = 16'b0;
            lr_valid_1_in = 1'b0;
            lr_valid_2_in = 1'b0;
            loss_data_1_in = 16'b0;
            loss_data_2_in = 16'b0;
            loss_valid_1_in = 1'b0;
            loss_valid_2_in = 1'b0;
            lr_d_data_1_in = 16'b0;
            lr_d_data_2_in = 16'b0;
            lr_d_valid_1_in = 1'b0;
            lr_d_valid_2_in = 1'b0;
        end else begin
            // bias module
            if(vpu_data_pathway[3]) begin
                // connect vpu inputs to bias module
                bias_data_1_in = vpu_data_in_1;
                bias_data_2_in = vpu_data_in_2;
                bias_valid_1_in = vpu_valid_in_1;
                bias_valid_2_in = vpu_valid_in_2;

                // connect bias output to intermediate values
                b_to_lr_data_in_1 = bias_z_data_out_1;
                b_to_lr_data_in_2 = bias_z_data_out_2;
                b_to_lr_valid_in_1 = bias_valid_1_out;
                b_to_lr_valid_in_2 = bias_valid_2_out;
            end else begin
                // disable inputs
                bias_data_1_in = 16'b0;
                bias_data_2_in = 16'b0;
                bias_valid_1_in = 1'b0;
                bias_valid_2_in = 1'b0;

                // connect vpu input to intermediate values
                b_to_lr_data_in_1 = vpu_data_in_1;
                b_to_lr_data_in_2 = vpu_data_in_2;
                b_to_lr_valid_in_1 = vpu_valid_in_1;
                b_to_lr_valid_in_2 = vpu_valid_in_2;
            end

            // leaky relu module
            if(vpu_data_pathway[2]) begin
                // connect lr inputs to intermediate values
                lr_data_1_in = b_to_lr_data_in_1;
                lr_data_2_in = b_to_lr_data_in_2;
                lr_valid_1_in = b_to_lr_valid_in_1;
                lr_valid_2_in = b_to_lr_valid_in_2;

                // connect lr outputs to intermediate values
                lr_to_loss_data_in_1 = lr_data_1_out;
                lr_to_loss_data_in_2 = lr_data_2_out;
                lr_to_loss_valid_in_1 = lr_valid_1_out;
                lr_to_loss_valid_in_2 = lr_valid_2_out;

            end else begin
                // disable inputs
                lr_data_1_in = 16'b0;
                lr_data_2_in = 16'b0;
                lr_valid_1_in = 1'b0;
                lr_valid_2_in = 1'b0;

                // connect intermediate values to each other
                lr_to_loss_data_in_1 = b_to_lr_data_in_1;
                lr_to_loss_data_in_2 = b_to_lr_data_in_2;
                lr_to_loss_valid_in_1 = b_to_lr_valid_in_1;
                lr_to_loss_valid_in_2 = b_to_lr_valid_in_2;
            end

            // loss module
            if(vpu_data_pathway[1]) begin
                // connect loss inputs to intermediate values
                loss_data_1_in = lr_to_loss_data_in_1;
                loss_data_2_in = lr_to_loss_data_in_2;
                loss_valid_1_in = lr_to_loss_valid_in_1;
                loss_valid_2_in = lr_to_loss_valid_in_2;

                // connect loss outputs to intermediate values
                loss_to_lrd_data_in_1 = loss_data_1_out;
                loss_to_lrd_data_in_2 = loss_data_2_out;
                loss_to_lrd_valid_in_1 = loss_valid_1_out;
                loss_to_lrd_valid_in_2 = loss_valid_2_out;

                // Cache and use 'last H matrix'
                last_H_data_1_in = lr_data_1_out;
                last_H_data_2_in = lr_data_2_out;
                lr_d_H_in_1 = last_H_data_1_out;
                lr_d_H_in_2 = last_H_data_2_out;
            end else begin
                // disable inputs
                loss_data_1_in = 16'b0;
                loss_data_2_in = 16'b0;
                loss_valid_1_in = 1'b0;
                loss_valid_2_in = 1'b0;

                // connect intermediate values to each other
                loss_to_lrd_data_in_1 = lr_to_loss_data_in_1;
                loss_to_lrd_data_in_2 = lr_to_loss_data_in_2;
                loss_to_lrd_valid_in_1 = lr_to_loss_valid_in_1;
                loss_to_lrd_valid_in_2 = lr_to_loss_valid_in_2;

                // Don't cache and use 'last H matrix'
                lr_d_H_in_1 = H_in_1;
                lr_d_H_in_2 = H_in_2;
            end

            // leaky relu derivative module
            if(vpu_data_pathway[0]) begin
                lr_d_data_1_in = loss_to_lrd_data_in_1;
                lr_d_data_2_in = loss_to_lrd_data_in_2;
                lr_d_valid_1_in = loss_to_lrd_valid_in_1;
                lr_d_valid_2_in = loss_to_lrd_valid_in_2;

                // connect lr_d outputs to vpu output
                vpu_data_out_1 = lr_d_data_1_out;
                vpu_data_out_2 = lr_d_data_2_out;
                vpu_valid_out_1 = lr_d_valid_1_out;
                vpu_valid_out_2 = lr_d_valid_2_out;
            end else begin
                // disable inputs
                lr_d_data_1_in = loss_to_lrd_data_in_1;
                lr_d_data_2_in = loss_to_lrd_data_in_2;
                lr_d_valid_1_in = loss_to_lrd_valid_in_1;
                lr_d_valid_2_in = loss_to_lrd_valid_in_2;

                // connect intermediate values to vpu output
                vpu_data_out_1 = loss_to_lrd_data_in_1;
                vpu_data_out_2 = loss_to_lrd_data_in_2;
                vpu_valid_out_1 = loss_to_lrd_valid_in_1;
                vpu_valid_out_2 = loss_to_lrd_valid_in_2;
            end
        end
    end

    // sequential logic to cache last H???
    always @(posedge clk or posedge rst) begin
        if (rst) begin
            last_H_data_1_in <= 0;
            last_H_data_2_in <= 0;
            last_H_data_1_out <= 0;
            last_H_data_2_out <= 0;
        end else begin
            if (vpu_data_pathway[1]) begin
                last_H_data_1_out <= last_H_data_1_in;
                last_H_data_2_out <= last_H_data_2_in;
            end else begin
                last_H_data_1_out <= 0;
                last_H_data_2_out <= 0;
            end 
        end
    end

endmodule
// -------- merged from tpu.sv --------

module tpu #(
    parameter int SYSTOLIC_ARRAY_WIDTH = 2
)(
    input logic clk,
    input logic rst,

    // UB wires (writing from host to UB)
    input logic [15:0] ub_wr_host_data_in [0:SYSTOLIC_ARRAY_WIDTH-1],
    input logic ub_wr_host_valid_in [0:SYSTOLIC_ARRAY_WIDTH-1],

    // UB wires (inputting reading instructions from host)
    input logic ub_rd_start_in,
    input logic ub_rd_transpose,
    input logic [8:0] ub_ptr_select,
    input logic [15:0] ub_rd_addr_in,
    input logic [15:0] ub_rd_row_size,
    input logic [15:0] ub_rd_col_size,

    // Learning rate
    input logic [15:0] learning_rate_in,

    // VPU data pathway
    input logic [3:0] vpu_data_pathway,

    input logic sys_switch_in,
    input logic [15:0] vpu_leak_factor_in,
    input logic [15:0] inv_batch_size_times_two_in
);
    // UB internal output wires
    logic [15:0] ub_wr_data_in [0:SYSTOLIC_ARRAY_WIDTH-1];
    logic ub_wr_valid_in [0:SYSTOLIC_ARRAY_WIDTH-1];

    // Number of columns in the matrix to send to systolic array to disable columns of PEs
    logic [15:0] ub_rd_col_size_out;
    logic ub_rd_col_size_valid_out;
    
    // Array wires for connection to unified_buffer
    logic [15:0] ub_rd_input_data_out_0;
    logic [15:0] ub_rd_input_data_out_1;
    logic ub_rd_input_valid_out_0;
    logic ub_rd_input_valid_out_1;

    logic [15:0] ub_rd_weight_data_out_0;
    logic [15:0] ub_rd_weight_data_out_1;
    logic ub_rd_weight_valid_out_0;
    logic ub_rd_weight_valid_out_1;

    logic [15:0] ub_rd_bias_data_out_0;
    logic [15:0] ub_rd_bias_data_out_1;
    
    logic [15:0] ub_rd_Y_data_out_0;
    logic [15:0] ub_rd_Y_data_out_1;

    logic [15:0] ub_rd_H_data_out_0;
    logic [15:0] ub_rd_H_data_out_1;

    // Systolic array internal output wires
    logic [15:0] sys_data_out_21;
    logic [15:0] sys_data_out_22;
    logic sys_valid_out_21;
    logic sys_valid_out_22;

    // VPU internal output wires
    logic [15:0] vpu_data_out_1;
    logic [15:0] vpu_data_out_2;
    logic vpu_valid_out_1;
    logic vpu_valid_out_2;

    assign ub_wr_data_in[0] = vpu_data_out_1;
    assign ub_wr_data_in[1] = vpu_data_out_2;
    assign ub_wr_valid_in[0] = vpu_valid_out_1;
    assign ub_wr_valid_in[1] = vpu_valid_out_2;
    
    unified_buffer #(
        .SYSTOLIC_ARRAY_WIDTH(SYSTOLIC_ARRAY_WIDTH)
    ) ub_inst(
        .clk(clk),
        .rst(rst),

        .ub_wr_data_in(ub_wr_data_in),
        .ub_wr_valid_in(ub_wr_valid_in),

        // Write ports from host to UB (for loading in parameters)
        .ub_wr_host_data_in(ub_wr_host_data_in),
        .ub_wr_host_valid_in(ub_wr_host_valid_in),

        // Read instruction input from instruction memory
        .ub_rd_start_in(ub_rd_start_in),
        .ub_rd_transpose(ub_rd_transpose),
        .ub_ptr_select(ub_ptr_select),
        .ub_rd_addr_in(ub_rd_addr_in),
        .ub_rd_row_size(ub_rd_row_size),
        .ub_rd_col_size(ub_rd_col_size),

        // Learning rate input
        .learning_rate_in(learning_rate_in),

        // Read ports from UB to left side of systolic array
        .ub_rd_input_data_out_0(ub_rd_input_data_out_0),
        .ub_rd_input_data_out_1(ub_rd_input_data_out_1),
        .ub_rd_input_valid_out_0(ub_rd_input_valid_out_0),
        .ub_rd_input_valid_out_1(ub_rd_input_valid_out_1),

        // Read ports from UB to top of systolic array
        .ub_rd_weight_data_out_0(ub_rd_weight_data_out_0),
        .ub_rd_weight_data_out_1(ub_rd_weight_data_out_1),
        .ub_rd_weight_valid_out_0(ub_rd_weight_valid_out_0),
        .ub_rd_weight_valid_out_1(ub_rd_weight_valid_out_1),

        // Read ports from UB to bias modules in VPU
        .ub_rd_bias_data_out_0(ub_rd_bias_data_out_0),
        .ub_rd_bias_data_out_1(ub_rd_bias_data_out_1),

        // Read ports from UB to loss modules (Y matrices) in VPU
        .ub_rd_Y_data_out_0(ub_rd_Y_data_out_0),
        .ub_rd_Y_data_out_1(ub_rd_Y_data_out_1),

        // Read ports from UB to activation derivative modules (H matrices) in VPU
        .ub_rd_H_data_out_0(ub_rd_H_data_out_0),
        .ub_rd_H_data_out_1(ub_rd_H_data_out_1),

        // Outputs to send number of columns to systolic array
        .ub_rd_col_size_out(ub_rd_col_size_out),
        .ub_rd_col_size_valid_out(ub_rd_col_size_valid_out)
    );

    systolic systolic_inst (
        .clk(clk),
        .rst(rst),

        // input signals from left side of systolic array
        .sys_data_in_11(ub_rd_input_data_out_0),
        .sys_data_in_21(ub_rd_input_data_out_1),
        .sys_start(ub_rd_input_valid_out_0),    // start signal
        // .sys_start_2(ub_rd_input_valid_out_1),    // start signal propagates only from left to right in row 2

        .sys_data_out_21(sys_data_out_21),
        .sys_data_out_22(sys_data_out_22),
        .sys_valid_out_21(sys_valid_out_21), 
        .sys_valid_out_22(sys_valid_out_22),

        // input signals from top of systolic array
        .sys_weight_in_11(ub_rd_weight_data_out_0), 
        .sys_weight_in_12(ub_rd_weight_data_out_1),
        .sys_accept_w_1(ub_rd_weight_valid_out_0),       // accept weight signal propagates only from top to bottom in column 1
        .sys_accept_w_2(ub_rd_weight_valid_out_1),       // accept weight signal propagates only from top to bottom in column 2

        .sys_switch_in(sys_switch_in),          // switch signal copies weight from shadow buffer to active buffer. propagates from top left to bottom right

        .ub_rd_col_size_in(ub_rd_col_size_out),
        .ub_rd_col_size_valid_in(ub_rd_col_size_valid_out)
    );

    vpu vpu_inst (
        .clk(clk),
        .rst(rst),

        .vpu_data_pathway(vpu_data_pathway), // 4-bits to signify which modules to route the inputs to (1 bit for each module)

        // Inputs from systolic array
        .vpu_data_in_1(sys_data_out_21),
        .vpu_data_in_2(sys_data_out_22),
        .vpu_valid_in_1(sys_valid_out_21),
        .vpu_valid_in_2(sys_valid_out_22),

        // Inputs from UB
        .bias_scalar_in_1(ub_rd_bias_data_out_0),               // For bias modules
        .bias_scalar_in_2(ub_rd_bias_data_out_1),               // For bias modules
        .lr_leak_factor_in(vpu_leak_factor_in),                 // For leaky relu modules
        .Y_in_1(ub_rd_Y_data_out_0),                                  // For loss modules
        .Y_in_2(ub_rd_Y_data_out_1),                                  // For loss modules
        .inv_batch_size_times_two_in(inv_batch_size_times_two_in),             // For loss modules
        .H_in_1(ub_rd_H_data_out_0),                                  // For leaky relu derivative modules (WE ONLY NEED THIS PORT FOR EVERY dL/dH after the first node)
        .H_in_2(ub_rd_H_data_out_1),                                  // For leaky relu derivative modules (WE ONLY NEED THIS PORT FOR EVERY dL/dH after the first node)

        // Outputs to UB
        .vpu_data_out_1(vpu_data_out_1),
        .vpu_data_out_2(vpu_data_out_2),
        .vpu_valid_out_1(vpu_valid_out_1),
        .vpu_valid_out_2(vpu_valid_out_2)
    ); 
endmodule
