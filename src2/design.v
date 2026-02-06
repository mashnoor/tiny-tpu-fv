`default_nettype none
module fxp_zoom (
	in,
	out,
	overflow
);
	parameter WII = 8;
	parameter WIF = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire [(WII + WIF) - 1:0] in;
	output wire [(WOI + WOF) - 1:0] out;
	output reg overflow;
	initial overflow = 1'b0;
	reg [(WII + WOF) - 1:0] inr = 0;
	reg [WII - 1:0] ini = 0;
	reg [WOI - 1:0] outi = 0;
	reg [WOF - 1:0] outf = 0;
	generate
		if (WOF < WIF) begin : genblk1
			if (ROUND == 0) begin : genblk1
				always @(*) inr = in[(WII + WIF) - 1:WIF - WOF];
			end
			else if ((WII + WOF) >= 2) begin : genblk1
				always @(*) begin
					inr = in[(WII + WIF) - 1:WIF - WOF];
					if (in[(WIF - WOF) - 1] & ~(~inr[(WII + WOF) - 1] & (&inr[(WII + WOF) - 2:0])))
						inr = inr + 1;
				end
			end
			else begin : genblk1
				always @(*) begin
					inr = in[(WII + WIF) - 1:WIF - WOF];
					if (in[(WIF - WOF) - 1] & inr[(WII + WOF) - 1])
						inr = inr + 1;
				end
			end
		end
		else if (WOF == WIF) begin : genblk1
			always @(*) inr[(WII + WOF) - 1:WOF - WIF] = in;
		end
		else begin : genblk1
			always @(*) begin
				inr[(WII + WOF) - 1:WOF - WIF] = in;
				inr[(WOF - WIF) - 1:0] = 0;
			end
		end
		if (WOI < WII) begin : genblk2
			always @(*) begin
				{ini, outf} = inr;
				if (~ini[WII - 1] & |ini[WII - 2:WOI - 1]) begin
					overflow = 1'b1;
					outi = {WOI {1'b1}};
					outi[WOI - 1] = 1'b0;
					outf = {WOF {1'b1}};
				end
				else if (ini[WII - 1] & ~(&ini[WII - 2:WOI - 1])) begin
					overflow = 1'b1;
					outi = 0;
					outi[WOI - 1] = 1'b1;
					outf = 0;
				end
				else begin
					overflow = 1'b0;
					outi = ini[WOI - 1:0];
				end
			end
		end
		else begin : genblk2
			always @(*) begin
				{ini, outf} = inr;
				overflow = 1'b0;
				outi = (ini[WII - 1] ? {WOI {1'b1}} : 0);
				outi[WII - 1:0] = ini;
			end
		end
	endgenerate
	assign out = {outi, outf};
endmodule
module fxp_add (
	ina,
	inb,
	out,
	overflow
);
	parameter WIIA = 8;
	parameter WIFA = 8;
	parameter WIIB = 8;
	parameter WIFB = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire [(WIIA + WIFA) - 1:0] ina;
	input wire [(WIIB + WIFB) - 1:0] inb;
	output wire [(WOI + WOF) - 1:0] out;
	output wire overflow;
	localparam WII = (WIIA > WIIB ? WIIA : WIIB);
	localparam WIF = (WIFA > WIFB ? WIFA : WIFB);
	localparam WRI = WII + 1;
	localparam WRF = WIF;
	wire [(WII + WIF) - 1:0] inaz;
	wire [(WII + WIF) - 1:0] inbz;
	wire signed [(WRI + WRF) - 1:0] res;
	assign res = $signed(inaz) + $signed(inbz);
	fxp_zoom #(
		.WII(WIIA),
		.WIF(WIFA),
		.WOI(WII),
		.WOF(WIF),
		.ROUND(0)
	) ina_zoom(
		.in(ina),
		.out(inaz),
		.overflow()
	);
	fxp_zoom #(
		.WII(WIIB),
		.WIF(WIFB),
		.WOI(WII),
		.WOF(WIF),
		.ROUND(0)
	) inb_zoom(
		.in(inb),
		.out(inbz),
		.overflow()
	);
	wire [(WRI + WRF) - 1:0] res_unsigned;
	assign res_unsigned = res;
	fxp_zoom #(
		.WII(WRI),
		.WIF(WRF),
		.WOI(WOI),
		.WOF(WOF),
		.ROUND(ROUND)
	) res_zoom(
		.in(res_unsigned),
		.out(out),
		.overflow(overflow)
	);
endmodule
module fxp_addsub (
	ina,
	inb,
	sub,
	out,
	overflow
);
	parameter WIIA = 8;
	parameter WIFA = 8;
	parameter WIIB = 8;
	parameter WIFB = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire [(WIIA + WIFA) - 1:0] ina;
	input wire [(WIIB + WIFB) - 1:0] inb;
	input wire sub;
	output wire [(WOI + WOF) - 1:0] out;
	output wire overflow;
	localparam WIIBE = WIIB + 1;
	localparam WII = (WIIA > WIIBE ? WIIA : WIIBE);
	localparam WIF = (WIFA > WIFB ? WIFA : WIFB);
	localparam WRI = WII + 1;
	localparam WRF = WIF;
	localparam [(WIIBE + WIFB) - 1:0] ONE = 1;
	wire [(WIIBE + WIFB) - 1:0] inbe;
	wire [(WII + WIF) - 1:0] inaz;
	wire [(WII + WIF) - 1:0] inbz;
	wire [(WIIBE + WIFB) - 1:0] inbv;
	wire signed [(WRI + WRF) - 1:0] res;
	wire [(WRI + WRF) - 1:0] res_unsigned;
	assign inbv = (sub ? ~inbe + ONE : inbe);
	assign res = $signed(inaz) + $signed(inbz);
	assign res_unsigned = res;
	fxp_zoom #(
		.WII(WIIB),
		.WIF(WIFB),
		.WOI(WIIBE),
		.WOF(WIFB),
		.ROUND(0)
	) inb_extend(
		.in(inb),
		.out(inbe),
		.overflow()
	);
	fxp_zoom #(
		.WII(WIIA),
		.WIF(WIFA),
		.WOI(WII),
		.WOF(WIF),
		.ROUND(0)
	) ina_zoom(
		.in(ina),
		.out(inaz),
		.overflow()
	);
	fxp_zoom #(
		.WII(WIIBE),
		.WIF(WIFB),
		.WOI(WII),
		.WOF(WIF),
		.ROUND(0)
	) inb_zoom(
		.in(inbv),
		.out(inbz),
		.overflow()
	);
	fxp_zoom #(
		.WII(WRI),
		.WIF(WRF),
		.WOI(WOI),
		.WOF(WOF),
		.ROUND(ROUND)
	) res_zoom(
		.in(res_unsigned),
		.out(out),
		.overflow(overflow)
	);
endmodule
module fxp_mul (
	ina,
	inb,
	out,
	overflow
);
	parameter WIIA = 8;
	parameter WIFA = 8;
	parameter WIIB = 8;
	parameter WIFB = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire [(WIIA + WIFA) - 1:0] ina;
	input wire [(WIIB + WIFB) - 1:0] inb;
	output wire [(WOI + WOF) - 1:0] out;
	output wire overflow;
	localparam WRI = WIIA + WIIB;
	localparam WRF = WIFA + WIFB;
	wire signed [(WRI + WRF) - 1:0] res;
	wire [(WRI + WRF) - 1:0] res_unsigned;
	assign res = $signed(ina) * $signed(inb);
	assign res_unsigned = res;
	fxp_zoom #(
		.WII(WRI),
		.WIF(WRF),
		.WOI(WOI),
		.WOF(WOF),
		.ROUND(ROUND)
	) res_zoom(
		.in(res_unsigned),
		.out(out),
		.overflow(overflow)
	);
endmodule
module fxp_mul_pipe (
	rstn,
	clk,
	ina,
	inb,
	out,
	overflow
);
	parameter WIIA = 8;
	parameter WIFA = 8;
	parameter WIIB = 8;
	parameter WIFB = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire rstn;
	input wire clk;
	input wire [(WIIA + WIFA) - 1:0] ina;
	input wire [(WIIB + WIFB) - 1:0] inb;
	output reg [(WOI + WOF) - 1:0] out;
	output reg overflow;
	initial {out, overflow} = 0;
	localparam WRI = WIIA + WIIB;
	localparam WRF = WIFA + WIFB;
	wire [(WOI + WOF) - 1:0] outc;
	wire overflowc;
	reg signed [(WRI + WRF) - 1:0] res = 0;
	wire [(WRI + WRF) - 1:0] res_unsigned;
	assign res_unsigned = res;
	always @(posedge clk or negedge rstn)
		if (~rstn)
			res <= 0;
		else
			res <= $signed(ina) * $signed(inb);
	fxp_zoom #(
		.WII(WRI),
		.WIF(WRF),
		.WOI(WOI),
		.WOF(WOF),
		.ROUND(ROUND)
	) res_zoom(
		.in(res_unsigned),
		.out(outc),
		.overflow(overflowc)
	);
	always @(posedge clk or negedge rstn)
		if (~rstn) begin
			out <= 0;
			overflow <= 1'b0;
		end
		else begin
			out <= outc;
			overflow <= overflowc;
		end
endmodule
module fxp_div (
	dividend,
	divisor,
	out,
	overflow
);
	parameter WIIA = 8;
	parameter WIFA = 8;
	parameter WIIB = 8;
	parameter WIFB = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire [(WIIA + WIFA) - 1:0] dividend;
	input wire [(WIIB + WIFB) - 1:0] divisor;
	output reg [(WOI + WOF) - 1:0] out;
	output reg overflow;
	initial {out, overflow} = 0;
	localparam WRI = ((WOI + WIIB) > WIIA ? WOI + WIIB : WIIA);
	localparam WRF = ((WOF + WIFB) > WIFA ? WOF + WIFB : WIFA);
	reg sign = 1'b0;
	reg [(WIIA + WIFA) - 1:0] udividend = 0;
	reg [(WIIB + WIFB) - 1:0] udivisor = 0;
	reg [(WRI + WRF) - 1:0] acc = 0;
	reg [(WRI + WRF) - 1:0] acct = 0;
	wire [(WRI + WRF) - 1:0] divd;
	wire [(WRI + WRF) - 1:0] divr;
	localparam [(WIIA + WIFA) - 1:0] ONEA = 1;
	localparam [(WIIB + WIFB) - 1:0] ONEB = 1;
	localparam [(WOI + WOF) - 1:0] ONEO = 1;
	always @(*) begin
		sign = dividend[(WIIA + WIFA) - 1] ^ divisor[(WIIB + WIFB) - 1];
		udividend = (dividend[(WIIA + WIFA) - 1] ? ~dividend + ONEA : dividend);
		udivisor = (divisor[(WIIB + WIFB) - 1] ? ~divisor + ONEB : divisor);
	end
	fxp_zoom #(
		.WII(WIIA),
		.WIF(WIFA),
		.WOI(WRI),
		.WOF(WRF),
		.ROUND(0)
	) dividend_zoom(
		.in(udividend),
		.out(divd),
		.overflow()
	);
	fxp_zoom #(
		.WII(WIIB),
		.WIF(WIFB),
		.WOI(WRI),
		.WOF(WRF),
		.ROUND(0)
	) divisor_zoom(
		.in(udivisor),
		.out(divr),
		.overflow()
	);
	integer shamt;
	always @(*) begin
		acc = 0;
		for (shamt = WOI - 1; shamt >= -WOF; shamt = shamt - 1)
			begin
				if (shamt >= 0)
					acct = acc + (divr << shamt);
				else
					acct = acc + (divr >> -shamt);
				if (acct <= divd) begin
					acc = acct;
					out[WOF + shamt] = 1'b1;
				end
				else
					out[WOF + shamt] = 1'b0;
			end
		if (ROUND && ~(&out)) begin
			acct = acc + (divr >> WOF);
			if ((acct - divd) < (divd - acc))
				out = out + 1;
		end
		overflow = 1'b0;
		if (sign) begin
			if (out[(WOI + WOF) - 1]) begin
				if (|out[(WOI + WOF) - 2:0])
					overflow = 1'b1;
				out[(WOI + WOF) - 1] = 1'b1;
				out[(WOI + WOF) - 2:0] = 0;
			end
			else
				out = ~out + ONEO;
		end
		else if (out[(WOI + WOF) - 1]) begin
			overflow = 1'b1;
			out[(WOI + WOF) - 1] = 1'b0;
			out[(WOI + WOF) - 2:0] = {WOI + WOF {1'b1}};
		end
	end
endmodule
module fxp_div_pipe (
	rstn,
	clk,
	dividend,
	divisor,
	out,
	overflow
);
	parameter WIIA = 8;
	parameter WIFA = 8;
	parameter WIIB = 8;
	parameter WIFB = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire rstn;
	input wire clk;
	input wire [(WIIA + WIFA) - 1:0] dividend;
	input wire [(WIIB + WIFB) - 1:0] divisor;
	output reg [(WOI + WOF) - 1:0] out;
	output reg overflow;
	initial {out, overflow} = 0;
	localparam WRI = ((WOI + WIIB) > WIIA ? WOI + WIIB : WIIA);
	localparam WRF = ((WOF + WIFB) > WIFA ? WOF + WIFB : WIFA);
	wire [(WRI + WRF) - 1:0] divd;
	wire [(WRI + WRF) - 1:0] divr;
	reg [(WOI + WOF) - 1:0] roundedres = 0;
	reg rsign = 1'b0;
	reg sign [WOI + WOF:0];
	reg [(WRI + WRF) - 1:0] acc [WOI + WOF:0];
	reg [(WRI + WRF) - 1:0] divdp [WOI + WOF:0];
	reg [(WRI + WRF) - 1:0] divrp [WOI + WOF:0];
	reg [(WOI + WOF) - 1:0] res [WOI + WOF:0];
	localparam [(WOI + WOF) - 1:0] ONEO = 1;
	integer ii;
	initial for (ii = 0; ii <= (WOI + WOF); ii = ii + 1)
		begin
			res[ii] = 0;
			divrp[ii] = 0;
			divdp[ii] = 0;
			acc[ii] = 0;
			sign[ii] = 1'b0;
		end
	wire [(WIIA + WIFA) - 1:0] ONEA = 1;
	wire [(WIIB + WIFB) - 1:0] ONEB = 1;
	wire [(WIIA + WIFA) - 1:0] udividend = (dividend[(WIIA + WIFA) - 1] ? ~dividend + ONEA : dividend);
	wire [(WIIB + WIFB) - 1:0] udivisor = (divisor[(WIIB + WIFB) - 1] ? ~divisor + ONEB : divisor);
	fxp_zoom #(
		.WII(WIIA),
		.WIF(WIFA),
		.WOI(WRI),
		.WOF(WRF),
		.ROUND(0)
	) dividend_zoom(
		.in(udividend),
		.out(divd),
		.overflow()
	);
	fxp_zoom #(
		.WII(WIIB),
		.WIF(WIFB),
		.WOI(WRI),
		.WOF(WRF),
		.ROUND(0)
	) divisor_zoom(
		.in(udivisor),
		.out(divr),
		.overflow()
	);
	always @(posedge clk or negedge rstn)
		if (~rstn) begin
			res[0] <= 0;
			acc[0] <= 0;
			divdp[0] <= 0;
			divrp[0] <= 0;
			sign[0] <= 1'b0;
		end
		else begin
			res[0] <= 0;
			acc[0] <= 0;
			divdp[0] <= divd;
			divrp[0] <= divr;
			sign[0] <= dividend[(WIIA + WIFA) - 1] ^ divisor[(WIIB + WIFB) - 1];
		end
	reg [(WRI + WRF) - 1:0] tmp;
	always @(posedge clk or negedge rstn)
		if (~rstn)
			for (ii = 0; ii < (WOI + WOF); ii = ii + 1)
				begin
					res[ii + 1] <= 0;
					divrp[ii + 1] <= 0;
					divdp[ii + 1] <= 0;
					acc[ii + 1] <= 0;
					sign[ii + 1] <= 1'b0;
				end
		else
			for (ii = 0; ii < (WOI + WOF); ii = ii + 1)
				begin
					res[ii + 1] <= res[ii];
					divdp[ii + 1] <= divdp[ii];
					divrp[ii + 1] <= divrp[ii];
					sign[ii + 1] <= sign[ii];
					if (ii < WOI)
						tmp = acc[ii] + (divrp[ii] << ((WOI - 1) - ii));
					else
						tmp = acc[ii] + (divrp[ii] >> ((1 + ii) - WOI));
					if (tmp < divdp[ii]) begin
						acc[ii + 1] <= tmp;
						res[ii + 1][((WOF + WOI) - 1) - ii] <= 1'b1;
					end
					else begin
						acc[ii + 1] <= acc[ii];
						res[ii + 1][((WOF + WOI) - 1) - ii] <= 1'b0;
					end
				end
	always @(posedge clk or negedge rstn)
		if (~rstn) begin
			roundedres <= 0;
			rsign <= 1'b0;
		end
		else begin
			if ((ROUND && ~(&res[WOI + WOF])) && (((acc[WOI + WOF] + (divrp[WOI + WOF] >> WOF)) - divdp[WOI + WOF]) < (divdp[WOI + WOF] - acc[WOI + WOF])))
				roundedres <= res[WOI + WOF] + ONEO;
			else
				roundedres <= res[WOI + WOF];
			rsign <= sign[WOI + WOF];
		end
	always @(posedge clk or negedge rstn)
		if (~rstn) begin
			overflow <= 1'b0;
			out <= 0;
		end
		else begin
			overflow <= 1'b0;
			if (rsign) begin
				if (roundedres[(WOI + WOF) - 1]) begin
					if (|roundedres[(WOI + WOF) - 2:0])
						overflow <= 1'b1;
					out[(WOI + WOF) - 1] <= 1'b1;
					out[(WOI + WOF) - 2:0] <= 0;
				end
				else
					out <= ~roundedres + ONEO;
			end
			else if (roundedres[(WOI + WOF) - 1]) begin
				overflow <= 1'b1;
				out[(WOI + WOF) - 1] <= 1'b0;
				out[(WOI + WOF) - 2:0] <= {WOI + WOF {1'b1}};
			end
			else
				out <= roundedres;
		end
endmodule
module fxp_sqrt (
	in,
	out,
	overflow
);
	parameter WII = 8;
	parameter WIF = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire [(WII + WIF) - 1:0] in;
	output wire [(WOI + WOF) - 1:0] out;
	output wire overflow;
	localparam WTI = ((WII % 2) == 1 ? WII + 1 : WII);
	localparam WRI = WTI / 2;
	localparam [(WII + WIF) - 1:0] ONEI = 1;
	localparam [(WTI + WIF) - 1:0] ONET = 1;
	localparam [(WRI + WIF) - 1:0] ONER = 1;
	reg [WRI + WIF:0] resushort = 0;
	integer ii;
	reg sign;
	reg [(WTI + WIF) - 1:0] inu;
	reg [(WTI + WIF) - 1:0] resu2;
	reg [(WTI + WIF) - 1:0] resu2tmp;
	reg [(WTI + WIF) - 1:0] resu;
	always @(*) begin
		sign = in[(WII + WIF) - 1];
		inu = 0;
		inu[(WII + WIF) - 1:0] = (sign ? ~in + ONEI : in);
		{resu2, resu} = 0;
		for (ii = WRI - 1; ii >= -WIF; ii = ii - 1)
			begin
				resu2tmp = resu2;
				if (ii >= 0)
					resu2tmp = resu2tmp + (resu << (1 + ii));
				else
					resu2tmp = resu2tmp + (resu >> -(1 + ii));
				if (((2 * ii) + WIF) >= 0)
					resu2tmp = resu2tmp + (ONET << ((2 * ii) + WIF));
				if ((resu2tmp <= inu) && (inu != 0)) begin
					resu[ii + WIF] = 1'b1;
					resu2 = resu2tmp;
				end
			end
		resushort = (sign ? ~resu[WRI + WIF:0] + ONER : resu[WRI + WIF:0]);
	end
	fxp_zoom #(
		.WII(WRI + 1),
		.WIF(WIF),
		.WOI(WOI),
		.WOF(WOF),
		.ROUND(ROUND)
	) res_zoom(
		.in(resushort),
		.out(out),
		.overflow(overflow)
	);
endmodule
module fxp_sqrt_pipe (
	rstn,
	clk,
	in,
	out,
	overflow
);
	parameter WII = 8;
	parameter WIF = 8;
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire rstn;
	input wire clk;
	input wire [(WII + WIF) - 1:0] in;
	output reg [(WOI + WOF) - 1:0] out;
	output reg overflow;
	initial {overflow, out} = 0;
	localparam WTI = ((WII % 2) == 1 ? WII + 1 : WII);
	localparam WRI = WTI / 2;
	localparam [(WII + WIF) - 1:0] ONEI = 1;
	localparam [(WTI + WIF) - 1:0] ONET = 1;
	localparam [(WRI + WIF) - 1:0] ONER = 1;
	reg sign [WRI + WIF:0];
	reg [(WTI + WIF) - 1:0] inu [WRI + WIF:0];
	reg [(WTI + WIF) - 1:0] resu2 [WRI + WIF:0];
	reg [(WTI + WIF) - 1:0] resu [WRI + WIF:0];
	integer ii;
	integer jj;
	reg [(WTI + WIF) - 1:0] resu2tmp;
	initial for (ii = 0; ii <= (WRI + WIF); ii = ii + 1)
		begin
			sign[ii] = 0;
			inu[ii] = 0;
			resu2[ii] = 0;
			resu[ii] = 0;
		end
	always @(posedge clk or negedge rstn)
		if (~rstn)
			for (ii = 0; ii <= (WRI + WIF); ii = ii + 1)
				begin
					sign[ii] <= 0;
					inu[ii] <= 0;
					resu2[ii] <= 0;
					resu[ii] <= 0;
				end
		else begin
			sign[0] <= in[(WII + WIF) - 1];
			inu[0] <= 0;
			inu[0][(WII + WIF) - 1:0] <= (in[(WII + WIF) - 1] ? ~in + ONEI : in);
			resu2[0] <= 0;
			resu[0] <= 0;
			for (ii = WRI - 1; ii >= -WIF; ii = ii - 1)
				begin
					jj = (WRI - 1) - ii;
					sign[jj + 1] <= sign[jj];
					inu[jj + 1] <= inu[jj];
					resu[jj + 1] <= resu[jj];
					resu2[jj + 1] <= resu2[jj];
					resu2tmp = resu2[jj];
					if (ii >= 0)
						resu2tmp = resu2tmp + (resu[jj] << (1 + ii));
					else
						resu2tmp = resu2tmp + (resu[jj] >> -(1 + ii));
					if (((2 * ii) + WIF) >= 0)
						resu2tmp = resu2tmp + (ONET << ((2 * ii) + WIF));
					if ((resu2tmp <= inu[jj]) && (inu[jj] != 0)) begin
						resu[jj + 1][ii + WIF] <= 1'b1;
						resu2[jj + 1] <= resu2tmp;
					end
				end
		end
	wire [WRI + WIF:0] resushort = (sign[WRI + WIF] ? ~resu[WRI + WIF][WRI + WIF:0] + ONER : resu[WRI + WIF][WRI + WIF:0]);
	wire [(WOI + WOF) - 1:0] outl;
	wire overflowl;
	fxp_zoom #(
		.WII(WRI + 1),
		.WIF(WIF),
		.WOI(WOI),
		.WOF(WOF),
		.ROUND(ROUND)
	) res_zoom(
		.in(resushort),
		.out(outl),
		.overflow(overflowl)
	);
	always @(posedge clk or negedge rstn)
		if (~rstn)
			{overflow, out} <= 0;
		else
			{overflow, out} <= {overflowl, outl};
endmodule
module fxp2float (
	in,
	out
);
	parameter WII = 8;
	parameter WIF = 8;
	input wire [(WII + WIF) - 1:0] in;
	output reg [31:0] out;
	initial out = 0;
	localparam [(WII + WIF) - 1:0] ONEI = 1;
	wire sign = in[(WII + WIF) - 1];
	wire [(WII + WIF) - 1:0] inu = (sign ? ~in + ONEI : in);
	integer jj;
	reg flag;
	reg signed [9:0] expz;
	reg signed [9:0] ii;
	reg [7:0] expt;
	reg [22:0] tail;
	always @(*) begin
		tail = 0;
		flag = 1'b0;
		ii = 10'd22;
		expz = 0;
		for (jj = (WII + WIF) - 1; jj >= 0; jj = jj - 1)
			begin
				if (flag && (ii >= 0)) begin
					tail[ii] = inu[jj];
					ii = ii - 1;
				end
				if (inu[jj]) begin
					if (~flag)
						expz = (jj + 127) - WIF;
					flag = 1'b1;
				end
			end
		if (expz < $signed(10'd255))
			expt = (inu == 0 ? 0 : expz[7:0]);
		else begin
			expt = 8'd254;
			tail = 23'h7fffff;
		end
		out = {sign, expt, tail};
	end
endmodule
module fxp2float_pipe (
	rstn,
	clk,
	in,
	out
);
	parameter WII = 8;
	parameter WIF = 8;
	input wire rstn;
	input wire clk;
	input wire [(WII + WIF) - 1:0] in;
	output wire [31:0] out;
	reg sign [WII + WIF:0];
	reg [9:0] exp [WII + WIF:0];
	reg [(WII + WIF) - 1:0] inu [WII + WIF:0];
	localparam [(WII + WIF) - 1:0] ONEI = 1;
	reg [23:0] vall = 0;
	reg [23:0] valo = 0;
	reg [7:0] expo = 0;
	reg signo = 0;
	assign out = {signo, expo, valo[22:0]};
	integer ii;
	initial for (ii = WII + WIF; ii >= 0; ii = ii - 1)
		begin
			sign[ii] = 0;
			exp[ii] = 0;
			inu[ii] = 0;
		end
	always @(posedge clk or negedge rstn)
		if (~rstn)
			for (ii = WII + WIF; ii >= 0; ii = ii - 1)
				begin
					sign[ii] <= 0;
					exp[ii] <= 0;
					inu[ii] <= 0;
				end
		else begin
			sign[WII + WIF] <= in[(WII + WIF) - 1];
			exp[WII + WIF] <= WII + 126;
			inu[WII + WIF] <= (in[(WII + WIF) - 1] ? ~in + ONEI : in);
			for (ii = (WII + WIF) - 1; ii >= 0; ii = ii - 1)
				begin
					sign[ii] <= sign[ii + 1];
					if (inu[ii + 1][(WII + WIF) - 1]) begin
						exp[ii] <= exp[ii + 1];
						inu[ii] <= inu[ii + 1];
					end
					else begin
						if (exp[ii + 1] != 0)
							exp[ii] <= exp[ii + 1] - 10'd1;
						else
							exp[ii] <= exp[ii + 1];
						inu[ii] <= inu[ii + 1] << 1;
					end
				end
		end
	generate
		if (23 > ((WII + WIF) - 1)) begin : genblk1
			always @(*) begin
				vall = 0;
				vall[23:24 - (WII + WIF)] = inu[0];
			end
		end
		else begin : genblk1
			always @(*) vall = inu[0][(WII + WIF) - 1:(WII + WIF) - 24];
		end
	endgenerate
	always @(posedge clk or negedge rstn)
		if (~rstn)
			{signo, expo, valo} <= 0;
		else begin
			signo <= sign[0];
			if (exp[0] >= 10'd255) begin
				expo <= 8'd255;
				valo <= 24'hffffff;
			end
			else if ((exp[0] == 10'd0) || ~vall[23]) begin
				expo <= 8'd0;
				valo <= 0;
			end
			else begin
				expo <= exp[0][7:0];
				valo <= vall;
			end
		end
endmodule
module float2fxp (
	in,
	out,
	overflow
);
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire [31:0] in;
	output reg [(WOI + WOF) - 1:0] out;
	output reg overflow;
	initial {out, overflow} = 0;
	localparam [(WOI + WOF) - 1:0] ONEO = 1;
	integer ii;
	reg round;
	reg sign;
	reg [7:0] exp2;
	reg [23:0] val;
	reg signed [31:0] expi;
	always @(*) begin
		round = 0;
		overflow = 0;
		{sign, exp2, val[22:0]} = in;
		val[23] = 1'b1;
		out = 0;
		expi = (exp2 - 127) + WOF;
		if (&exp2)
			overflow = 1'b1;
		else if (in[30:0] != 0) begin
			for (ii = 23; ii >= 0; ii = ii - 1)
				begin
					if (val[ii]) begin
						if (expi >= ((WOI + WOF) - 1))
							overflow = 1'b1;
						else if (expi >= 0)
							out[expi] = 1'b1;
						else if (ROUND && (expi == -1))
							round = 1'b1;
					end
					expi = expi - 1;
				end
			if (round)
				out = out + 1;
		end
		if (overflow) begin
			if (sign) begin
				out[(WOI + WOF) - 1] = 1'b1;
				out[(WOI + WOF) - 2:0] = 0;
			end
			else begin
				out[(WOI + WOF) - 1] = 1'b0;
				out[(WOI + WOF) - 2:0] = {WOI + WOF {1'b1}};
			end
		end
		else if (sign)
			out = ~out + ONEO;
	end
endmodule
module float2fxp_pipe (
	rstn,
	clk,
	in,
	out,
	overflow
);
	parameter WOI = 8;
	parameter WOF = 8;
	parameter ROUND = 1;
	input wire rstn;
	input wire clk;
	input wire [31:0] in;
	output reg [(WOI + WOF) - 1:0] out;
	output reg overflow;
	localparam [(WOI + WOF) - 1:0] ONEO = 1;
	initial {out, overflow} = 0;
	wire sign;
	wire [7:0] exp;
	wire [23:0] val;
	assign {sign, exp, val[22:0]} = in;
	assign val[23] = |exp;
	reg signinit = 1'b0;
	reg roundinit = 1'b0;
	reg signed [31:0] expinit = 0;
	reg [(WOI + WOF) - 1:0] outinit = 0;
	generate
		if (((WOI + WOF) - 1) >= 23) begin : genblk1
			always @(posedge clk or negedge rstn)
				if (~rstn) begin
					outinit <= 0;
					roundinit <= 1'b0;
				end
				else begin
					outinit <= 0;
					outinit[(WOI + WOF) - 1:(WOI + WOF) - 24] <= val;
					roundinit <= 1'b0;
				end
		end
		else begin : genblk1
			always @(posedge clk or negedge rstn)
				if (~rstn) begin
					outinit <= 0;
					roundinit <= 1'b0;
				end
				else begin
					outinit <= val[23:24 - (WOI + WOF)];
					roundinit <= ROUND && val[(24 - (WOI + WOF)) - 1];
				end
		end
	endgenerate
	always @(posedge clk or negedge rstn)
		if (~rstn) begin
			signinit <= 1'b0;
			expinit <= 0;
		end
		else begin
			signinit <= sign;
			if ((exp == 8'd255) || ({24'd0, exp} > (WOI + 126)))
				expinit <= 0;
			else
				expinit <= ({24'd0, exp} - (WOI - 1)) - 127;
		end
	reg signs [WOI + WOF:0];
	reg rounds [WOI + WOF:0];
	reg [31:0] exps [WOI + WOF:0];
	reg [(WOI + WOF) - 1:0] outs [WOI + WOF:0];
	integer ii;
	always @(posedge clk or negedge rstn)
		if (~rstn)
			for (ii = 0; ii < ((WOI + WOF) + 1); ii = ii + 1)
				begin
					signs[ii] <= 0;
					rounds[ii] <= 0;
					exps[ii] <= 0;
					outs[ii] <= 0;
				end
		else begin
			for (ii = 0; ii < (WOI + WOF); ii = ii + 1)
				begin
					signs[ii] <= signs[ii + 1];
					if (exps[ii + 1] != 0) begin
						{outs[ii], rounds[ii]} <= {1'b0, outs[ii + 1]};
						exps[ii] <= exps[ii + 1] + 1;
					end
					else begin
						{outs[ii], rounds[ii]} <= {outs[ii + 1], rounds[ii + 1]};
						exps[ii] <= exps[ii + 1];
					end
				end
			signs[WOI + WOF] <= signinit;
			rounds[WOI + WOF] <= roundinit;
			exps[WOI + WOF] <= expinit;
			outs[WOI + WOF] <= outinit;
		end
	reg signl = 1'b0;
	reg [(WOI + WOF) - 1:0] outl = 0;
	reg [(WOI + WOF) - 1:0] outt;
	always @(posedge clk or negedge rstn)
		if (~rstn) begin
			outl <= 0;
			signl <= 1'b0;
		end
		else begin
			outt = outs[0];
			if ((ROUND & rounds[0]) & ~(&outt))
				outt = outt + 1;
			if (signs[0]) begin
				signl <= outt != 0;
				outt = ~outt + ONEO;
			end
			else
				signl <= 1'b0;
			outl <= outt;
		end
	always @(posedge clk or negedge rstn)
		if (~rstn) begin
			out <= 0;
			overflow <= 1'b0;
		end
		else begin
			out <= outl;
			overflow <= 1'b0;
			if (signl) begin
				if (~outl[(WOI + WOF) - 1]) begin
					out[(WOI + WOF) - 1] <= 1'b1;
					out[(WOI + WOF) - 2:0] <= 0;
					overflow <= 1'b1;
				end
			end
			else if (outl[(WOI + WOF) - 1]) begin
				out[(WOI + WOF) - 1] <= 1'b0;
				out[(WOI + WOF) - 2:0] <= {WOI + WOF {1'b1}};
				overflow <= 1'b1;
			end
		end
endmodule
module pe (
	clk,
	rst,
	pe_psum_in,
	pe_weight_in,
	pe_accept_w_in,
	pe_input_in,
	pe_valid_in,
	pe_switch_in,
	pe_enabled,
	pe_psum_out,
	pe_weight_out,
	pe_input_out,
	pe_valid_out,
	pe_switch_out
);
	reg _sv2v_0;
	parameter signed [31:0] DATA_WIDTH = 16;
	input wire clk;
	input wire rst;
	input wire signed [15:0] pe_psum_in;
	input wire signed [15:0] pe_weight_in;
	input wire pe_accept_w_in;
	input wire signed [15:0] pe_input_in;
	input wire pe_valid_in;
	input wire pe_switch_in;
	input wire pe_enabled;
	output reg signed [15:0] pe_psum_out;
	output reg signed [15:0] pe_weight_out;
	output reg signed [15:0] pe_input_out;
	output reg pe_valid_out;
	output reg pe_switch_out;
	wire signed [15:0] mult_out;
	wire signed [15:0] mac_out;
	reg signed [15:0] weight_reg_active;
	reg signed [15:0] weight_reg_inactive;
	fxp_mul mult(
		.ina(pe_input_in),
		.inb(weight_reg_active),
		.out(mult_out),
		.overflow()
	);
	fxp_add adder(
		.ina(mult_out),
		.inb(pe_psum_in),
		.out(mac_out),
		.overflow()
	);
	always @(*) begin
		if (_sv2v_0)
			;
		if (pe_switch_in)
			weight_reg_active = weight_reg_inactive;
	end
	always @(posedge clk or posedge rst)
		if (rst || !pe_enabled) begin
			pe_input_out <= 16'b0000000000000000;
			weight_reg_active <= 16'b0000000000000000;
			weight_reg_inactive <= 16'b0000000000000000;
			pe_valid_out <= 0;
			pe_weight_out <= 16'b0000000000000000;
			pe_switch_out <= 0;
		end
		else begin
			pe_valid_out <= pe_valid_in;
			pe_switch_out <= pe_switch_in;
			if (pe_accept_w_in) begin
				weight_reg_inactive <= pe_weight_in;
				pe_weight_out <= pe_weight_in;
			end
			else
				pe_weight_out <= 0;
			if (pe_valid_in) begin
				pe_input_out <= pe_input_in;
				pe_psum_out <= mac_out;
			end
			else begin
				pe_valid_out <= 0;
				pe_psum_out <= 16'b0000000000000000;
			end
		end
	initial _sv2v_0 = 0;
endmodule
module bias_child (
	clk,
	rst,
	bias_scalar_in,
	bias_Z_valid_out,
	bias_sys_data_in,
	bias_sys_valid_in,
	bias_z_data_out
);
	input wire clk;
	input wire rst;
	input wire signed [15:0] bias_scalar_in;
	output reg bias_Z_valid_out;
	input wire signed [15:0] bias_sys_data_in;
	input wire bias_sys_valid_in;
	output reg signed [15:0] bias_z_data_out;
	wire signed [15:0] z_pre_activation;
	fxp_add add_inst(
		.ina(bias_sys_data_in),
		.inb(bias_scalar_in),
		.out(z_pre_activation)
	);
	always @(posedge clk or posedge rst)
		if (rst) begin
			bias_Z_valid_out <= 1'b0;
			bias_z_data_out <= 16'b0000000000000000;
		end
		else if (bias_sys_valid_in) begin
			bias_Z_valid_out <= 1'b1;
			bias_z_data_out <= z_pre_activation;
		end
		else begin
			bias_Z_valid_out <= 1'b0;
			bias_z_data_out <= 16'b0000000000000000;
		end
endmodule
module bias_parent (
	clk,
	rst,
	bias_scalar_in_1,
	bias_scalar_in_2,
	bias_Z_valid_out_1,
	bias_Z_valid_out_2,
	bias_sys_data_in_1,
	bias_sys_data_in_2,
	bias_sys_valid_in_1,
	bias_sys_valid_in_2,
	bias_z_data_out_1,
	bias_z_data_out_2
);
	input wire clk;
	input wire rst;
	input wire signed [15:0] bias_scalar_in_1;
	input wire signed [15:0] bias_scalar_in_2;
	output wire bias_Z_valid_out_1;
	output wire bias_Z_valid_out_2;
	input wire signed [15:0] bias_sys_data_in_1;
	input wire signed [15:0] bias_sys_data_in_2;
	input wire bias_sys_valid_in_1;
	input wire bias_sys_valid_in_2;
	output wire signed [15:0] bias_z_data_out_1;
	output wire signed [15:0] bias_z_data_out_2;
	bias_child column_1(
		.clk(clk),
		.rst(rst),
		.bias_scalar_in(bias_scalar_in_1),
		.bias_Z_valid_out(bias_Z_valid_out_1),
		.bias_sys_data_in(bias_sys_data_in_1),
		.bias_sys_valid_in(bias_sys_valid_in_1),
		.bias_z_data_out(bias_z_data_out_1)
	);
	bias_child column_2(
		.clk(clk),
		.rst(rst),
		.bias_scalar_in(bias_scalar_in_2),
		.bias_Z_valid_out(bias_Z_valid_out_2),
		.bias_sys_data_in(bias_sys_data_in_2),
		.bias_sys_valid_in(bias_sys_valid_in_2),
		.bias_z_data_out(bias_z_data_out_2)
	);
endmodule
module control_unit (
	instruction,
	sys_switch_in,
	ub_rd_start_in,
	ub_rd_transpose,
	ub_wr_host_valid_in_1,
	ub_wr_host_valid_in_2,
	ub_rd_col_size,
	ub_rd_row_size,
	ub_rd_addr_in,
	ub_ptr_sel,
	ub_wr_host_data_in_1,
	ub_wr_host_data_in_2,
	vpu_data_pathway,
	inv_batch_size_times_two_in,
	vpu_leak_factor_in
);
	input wire [87:0] instruction;
	output wire sys_switch_in;
	output wire ub_rd_start_in;
	output wire ub_rd_transpose;
	output wire ub_wr_host_valid_in_1;
	output wire ub_wr_host_valid_in_2;
	output wire [1:0] ub_rd_col_size;
	output wire [7:0] ub_rd_row_size;
	output wire [1:0] ub_rd_addr_in;
	output wire [2:0] ub_ptr_sel;
	output wire [15:0] ub_wr_host_data_in_1;
	output wire [15:0] ub_wr_host_data_in_2;
	output wire [3:0] vpu_data_pathway;
	output wire [15:0] inv_batch_size_times_two_in;
	output wire [15:0] vpu_leak_factor_in;
	assign sys_switch_in = instruction[0];
	assign ub_rd_start_in = instruction[1];
	assign ub_rd_transpose = instruction[2];
	assign ub_wr_host_valid_in_1 = instruction[3];
	assign ub_wr_host_valid_in_2 = instruction[4];
	assign ub_rd_col_size = instruction[6:5];
	assign ub_rd_row_size = instruction[14:7];
	assign ub_rd_addr_in = instruction[16:15];
	assign ub_ptr_sel = instruction[19:17];
	assign ub_wr_host_data_in_1 = instruction[35:20];
	assign ub_wr_host_data_in_2 = instruction[51:36];
	assign vpu_data_pathway = instruction[55:52];
	assign inv_batch_size_times_two_in = instruction[71:56];
	assign vpu_leak_factor_in = instruction[87:72];
endmodule
module gradient_descent (
	clk,
	rst,
	lr_in,
	value_old_in,
	grad_in,
	grad_descent_valid_in,
	grad_bias_or_weight,
	value_updated_out,
	grad_descent_done_out
);
	reg _sv2v_0;
	input wire clk;
	input wire rst;
	input wire [15:0] lr_in;
	input wire [15:0] value_old_in;
	input wire [15:0] grad_in;
	input wire grad_descent_valid_in;
	input wire grad_bias_or_weight;
	output reg [15:0] value_updated_out;
	output reg grad_descent_done_out;
	wire [15:0] sub_value_out;
	wire grad_descent_in_reg;
	reg [15:0] sub_in_a;
	wire [15:0] mul_out;
	fxp_mul mul_inst(
		.ina(grad_in),
		.inb(lr_in),
		.out(mul_out),
		.overflow()
	);
	fxp_addsub sub_inst(
		.ina(sub_in_a),
		.inb(mul_out),
		.sub(1'b1),
		.out(sub_value_out),
		.overflow()
	);
	always @(*) begin
		if (_sv2v_0)
			;
		case (grad_bias_or_weight)
			1'b0:
				if (grad_descent_done_out)
					sub_in_a = value_updated_out;
				else
					sub_in_a = value_old_in;
			1'b1: sub_in_a = value_old_in;
		endcase
	end
	always @(posedge clk or posedge rst)
		if (rst) begin
			sub_in_a <= 1'sb0;
			value_updated_out <= 1'sb0;
			grad_descent_done_out <= 1'sb0;
		end
		else begin
			grad_descent_done_out <= grad_descent_valid_in;
			if (grad_descent_valid_in)
				value_updated_out <= sub_value_out;
			else
				value_updated_out <= 1'sb0;
		end
	initial _sv2v_0 = 0;
endmodule
module leaky_relu_child (
	clk,
	rst,
	lr_valid_in,
	lr_data_in,
	lr_leak_factor_in,
	lr_data_out,
	lr_valid_out
);
	input wire clk;
	input wire rst;
	input wire lr_valid_in;
	input wire signed [15:0] lr_data_in;
	input wire signed [15:0] lr_leak_factor_in;
	output reg signed [15:0] lr_data_out;
	output reg lr_valid_out;
	wire signed [15:0] mul_out;
	fxp_mul mul_inst(
		.ina(lr_data_in),
		.inb(lr_leak_factor_in),
		.out(mul_out)
	);
	always @(posedge clk or posedge rst)
		if (rst) begin
			lr_data_out <= 16'b0000000000000000;
			lr_valid_out <= 0;
		end
		else if (lr_valid_in) begin
			if (lr_data_in >= 0)
				lr_data_out <= lr_data_in;
			else
				lr_data_out <= mul_out;
			lr_valid_out <= 1;
		end
		else begin
			lr_valid_out <= 0;
			lr_data_out <= 16'b0000000000000000;
		end
endmodule
module leaky_relu_derivative_child (
	clk,
	rst,
	lr_d_valid_in,
	lr_d_data_in,
	lr_leak_factor_in,
	lr_d_H_data_in,
	lr_d_valid_out,
	lr_d_data_out
);
	input wire clk;
	input wire rst;
	input wire lr_d_valid_in;
	input wire signed [15:0] lr_d_data_in;
	input wire signed [15:0] lr_leak_factor_in;
	input wire signed [15:0] lr_d_H_data_in;
	output reg lr_d_valid_out;
	output reg signed [15:0] lr_d_data_out;
	wire signed [15:0] mul_out;
	fxp_mul mul_inst(
		.ina(lr_d_data_in),
		.inb(lr_leak_factor_in),
		.out(mul_out)
	);
	always @(posedge clk or posedge rst)
		if (rst) begin
			lr_d_data_out <= 16'b0000000000000000;
			lr_d_valid_out <= 0;
		end
		else begin
			lr_d_valid_out <= lr_d_valid_in;
			if (lr_d_valid_in) begin
				if (lr_d_H_data_in >= 0)
					lr_d_data_out <= lr_d_data_in;
				else
					lr_d_data_out <= mul_out;
			end
			else
				lr_d_data_out <= 16'b0000000000000000;
		end
endmodule
module leaky_relu_derivative_parent (
	clk,
	rst,
	lr_leak_factor_in,
	lr_d_valid_1_in,
	lr_d_valid_2_in,
	lr_d_data_1_in,
	lr_d_data_2_in,
	lr_d_H_1_in,
	lr_d_H_2_in,
	lr_d_data_1_out,
	lr_d_data_2_out,
	lr_d_valid_1_out,
	lr_d_valid_2_out
);
	input wire clk;
	input wire rst;
	input wire signed [15:0] lr_leak_factor_in;
	input wire lr_d_valid_1_in;
	input wire lr_d_valid_2_in;
	input wire signed [15:0] lr_d_data_1_in;
	input wire signed [15:0] lr_d_data_2_in;
	input wire signed [15:0] lr_d_H_1_in;
	input wire signed [15:0] lr_d_H_2_in;
	output wire signed [15:0] lr_d_data_1_out;
	output wire signed [15:0] lr_d_data_2_out;
	output wire lr_d_valid_1_out;
	output wire lr_d_valid_2_out;
	leaky_relu_derivative_child lr_d_col_1(
		.clk(clk),
		.rst(rst),
		.lr_d_valid_in(lr_d_valid_1_in),
		.lr_d_data_in(lr_d_data_1_in),
		.lr_leak_factor_in(lr_leak_factor_in),
		.lr_d_data_out(lr_d_data_1_out),
		.lr_d_valid_out(lr_d_valid_1_out),
		.lr_d_H_data_in(lr_d_H_1_in)
	);
	leaky_relu_derivative_child lr_d_col_2(
		.clk(clk),
		.rst(rst),
		.lr_d_valid_in(lr_d_valid_2_in),
		.lr_d_data_in(lr_d_data_2_in),
		.lr_leak_factor_in(lr_leak_factor_in),
		.lr_d_data_out(lr_d_data_2_out),
		.lr_d_valid_out(lr_d_valid_2_out),
		.lr_d_H_data_in(lr_d_H_2_in)
	);
endmodule
module leaky_relu_parent (
	clk,
	rst,
	lr_leak_factor_in,
	lr_valid_1_in,
	lr_valid_2_in,
	lr_data_1_in,
	lr_data_2_in,
	lr_data_1_out,
	lr_data_2_out,
	lr_valid_1_out,
	lr_valid_2_out
);
	input wire clk;
	input wire rst;
	input wire signed [15:0] lr_leak_factor_in;
	input wire lr_valid_1_in;
	input wire lr_valid_2_in;
	input wire signed [15:0] lr_data_1_in;
	input wire signed [15:0] lr_data_2_in;
	output wire signed [15:0] lr_data_1_out;
	output wire signed [15:0] lr_data_2_out;
	output wire lr_valid_1_out;
	output wire lr_valid_2_out;
	leaky_relu_child leaky_relu_col_1(
		.clk(clk),
		.rst(rst),
		.lr_valid_in(lr_valid_1_in),
		.lr_data_in(lr_data_1_in),
		.lr_leak_factor_in(lr_leak_factor_in),
		.lr_data_out(lr_data_1_out),
		.lr_valid_out(lr_valid_1_out)
	);
	leaky_relu_child leaky_relu_col_2(
		.clk(clk),
		.rst(rst),
		.lr_valid_in(lr_valid_2_in),
		.lr_data_in(lr_data_2_in),
		.lr_leak_factor_in(lr_leak_factor_in),
		.lr_data_out(lr_data_2_out),
		.lr_valid_out(lr_valid_2_out)
	);
endmodule
`default_nettype none
module loss_child (
	clk,
	rst,
	H_in,
	Y_in,
	valid_in,
	inv_batch_size_times_two_in,
	gradient_out,
	valid_out
);
	input wire clk;
	input wire rst;
	input wire signed [15:0] H_in;
	input wire signed [15:0] Y_in;
	input wire valid_in;
	input wire signed [15:0] inv_batch_size_times_two_in;
	output reg signed [15:0] gradient_out;
	output reg valid_out;
	wire signed [15:0] diff_stage1;
	wire signed [15:0] final_gradient;
	fxp_addsub subtractor(
		.ina(H_in),
		.inb(Y_in),
		.sub(1'b1),
		.out(diff_stage1),
		.overflow()
	);
	fxp_mul multiplier(
		.ina(diff_stage1),
		.inb(inv_batch_size_times_two_in),
		.out(final_gradient),
		.overflow()
	);
	always @(posedge clk or posedge rst)
		if (rst) begin
			gradient_out <= 1'sb0;
			valid_out <= 1'sb0;
		end
		else begin
			valid_out <= valid_in;
			gradient_out <= final_gradient;
		end
endmodule
module loss_parent (
	clk,
	rst,
	H_1_in,
	Y_1_in,
	H_2_in,
	Y_2_in,
	valid_1_in,
	valid_2_in,
	inv_batch_size_times_two_in,
	gradient_1_out,
	gradient_2_out,
	valid_1_out,
	valid_2_out
);
	input wire clk;
	input wire rst;
	input wire signed [15:0] H_1_in;
	input wire signed [15:0] Y_1_in;
	input wire signed [15:0] H_2_in;
	input wire signed [15:0] Y_2_in;
	input wire valid_1_in;
	input wire valid_2_in;
	input wire signed [15:0] inv_batch_size_times_two_in;
	output wire signed [15:0] gradient_1_out;
	output wire signed [15:0] gradient_2_out;
	output wire valid_1_out;
	output wire valid_2_out;
	loss_child first_column(
		.clk(clk),
		.rst(rst),
		.H_in(H_1_in),
		.Y_in(Y_1_in),
		.valid_in(valid_1_in),
		.inv_batch_size_times_two_in(inv_batch_size_times_two_in),
		.gradient_out(gradient_1_out),
		.valid_out(valid_1_out)
	);
	loss_child second_column(
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
module systolic (
	clk,
	rst,
	sys_data_in_11,
	sys_data_in_21,
	sys_start,
	sys_data_out_21,
	sys_data_out_22,
	sys_valid_out_21,
	sys_valid_out_22,
	sys_weight_in_11,
	sys_weight_in_12,
	sys_accept_w_1,
	sys_accept_w_2,
	sys_switch_in,
	ub_rd_col_size_in,
	ub_rd_col_size_valid_in
);
	parameter signed [31:0] SYSTOLIC_ARRAY_WIDTH = 2;
	input wire clk;
	input wire rst;
	input wire [15:0] sys_data_in_11;
	input wire [15:0] sys_data_in_21;
	input wire sys_start;
	output wire [15:0] sys_data_out_21;
	output wire [15:0] sys_data_out_22;
	output wire sys_valid_out_21;
	output wire sys_valid_out_22;
	input wire [15:0] sys_weight_in_11;
	input wire [15:0] sys_weight_in_12;
	input wire sys_accept_w_1;
	input wire sys_accept_w_2;
	input wire sys_switch_in;
	input wire [15:0] ub_rd_col_size_in;
	input wire ub_rd_col_size_valid_in;
	wire [15:0] pe_input_out_11;
	wire [15:0] pe_input_out_21;
	wire [15:0] pe_psum_out_11;
	wire [15:0] pe_psum_out_12;
	wire [15:0] pe_weight_out_11;
	wire [15:0] pe_weight_out_12;
	wire pe_switch_out_11;
	wire pe_switch_out_12;
	wire pe_valid_out_11;
	wire pe_valid_out_12;
	reg [1:0] pe_enabled;
	pe pe11(
		.clk(clk),
		.rst(rst),
		.pe_enabled(pe_enabled[0]),
		.pe_valid_in(sys_start),
		.pe_valid_out(pe_valid_out_11),
		.pe_accept_w_in(sys_accept_w_1),
		.pe_switch_in(sys_switch_in),
		.pe_switch_out(pe_switch_out_11),
		.pe_input_in(sys_data_in_11),
		.pe_psum_in(16'b0000000000000000),
		.pe_weight_in(sys_weight_in_11),
		.pe_input_out(pe_input_out_11),
		.pe_psum_out(pe_psum_out_11),
		.pe_weight_out(pe_weight_out_11)
	);
	pe pe12(
		.clk(clk),
		.rst(rst),
		.pe_enabled(pe_enabled[1]),
		.pe_valid_in(pe_valid_out_11),
		.pe_valid_out(pe_valid_out_12),
		.pe_accept_w_in(sys_accept_w_2),
		.pe_switch_in(pe_switch_out_11),
		.pe_switch_out(pe_switch_out_12),
		.pe_input_in(pe_input_out_11),
		.pe_psum_in(16'b0000000000000000),
		.pe_weight_in(sys_weight_in_12),
		.pe_input_out(),
		.pe_psum_out(pe_psum_out_12),
		.pe_weight_out(pe_weight_out_12)
	);
	pe pe21(
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
	pe pe22(
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
	always @(posedge clk or posedge rst)
		if (rst)
			pe_enabled <= 1'sb0;
		else if (ub_rd_col_size_valid_in)
			pe_enabled <= (1 << ub_rd_col_size_in) - 1;
endmodule
`default_nettype none
module unified_buffer (
	clk,
	rst,
	ub_wr_data_in,
	ub_wr_valid_in,
	ub_wr_host_data_in,
	ub_wr_host_valid_in,
	ub_rd_start_in,
	ub_rd_transpose,
	ub_ptr_select,
	ub_rd_addr_in,
	ub_rd_row_size,
	ub_rd_col_size,
	learning_rate_in,
	ub_rd_input_data_out_0,
	ub_rd_input_data_out_1,
	ub_rd_input_valid_out_0,
	ub_rd_input_valid_out_1,
	ub_rd_weight_data_out_0,
	ub_rd_weight_data_out_1,
	ub_rd_weight_valid_out_0,
	ub_rd_weight_valid_out_1,
	ub_rd_bias_data_out_0,
	ub_rd_bias_data_out_1,
	ub_rd_Y_data_out_0,
	ub_rd_Y_data_out_1,
	ub_rd_H_data_out_0,
	ub_rd_H_data_out_1,
	ub_rd_col_size_out,
	ub_rd_col_size_valid_out
);
	reg _sv2v_0;
	parameter signed [31:0] UNIFIED_BUFFER_WIDTH = 128;
	parameter signed [31:0] SYSTOLIC_ARRAY_WIDTH = 2;
	input wire clk;
	input wire rst;
	input wire [(SYSTOLIC_ARRAY_WIDTH * 16) - 1:0] ub_wr_data_in;
	input wire [0:SYSTOLIC_ARRAY_WIDTH - 1] ub_wr_valid_in;
	input wire [(SYSTOLIC_ARRAY_WIDTH * 16) - 1:0] ub_wr_host_data_in;
	input wire [0:SYSTOLIC_ARRAY_WIDTH - 1] ub_wr_host_valid_in;
	input wire ub_rd_start_in;
	input wire ub_rd_transpose;
	input wire [8:0] ub_ptr_select;
	input wire [15:0] ub_rd_addr_in;
	input wire [15:0] ub_rd_row_size;
	input wire [15:0] ub_rd_col_size;
	input wire [15:0] learning_rate_in;
	output wire [15:0] ub_rd_input_data_out_0;
	output wire [15:0] ub_rd_input_data_out_1;
	output wire ub_rd_input_valid_out_0;
	output wire ub_rd_input_valid_out_1;
	output wire [15:0] ub_rd_weight_data_out_0;
	output wire [15:0] ub_rd_weight_data_out_1;
	output wire ub_rd_weight_valid_out_0;
	output wire ub_rd_weight_valid_out_1;
	output wire [15:0] ub_rd_bias_data_out_0;
	output wire [15:0] ub_rd_bias_data_out_1;
	output wire [15:0] ub_rd_Y_data_out_0;
	output wire [15:0] ub_rd_Y_data_out_1;
	output wire [15:0] ub_rd_H_data_out_0;
	output wire [15:0] ub_rd_H_data_out_1;
	output reg [15:0] ub_rd_col_size_out;
	output reg ub_rd_col_size_valid_out;
	reg [15:0] ub_memory [0:UNIFIED_BUFFER_WIDTH - 1];
	reg [15:0] ub_rd_input_data_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg ub_rd_input_valid_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg [15:0] ub_rd_weight_data_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg ub_rd_weight_valid_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg [15:0] ub_rd_bias_data_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg [15:0] ub_rd_Y_data_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg [15:0] ub_rd_H_data_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg [15:0] wr_ptr;
	reg [15:0] rd_input_ptr;
	reg [15:0] rd_input_row_size;
	reg [15:0] rd_input_col_size;
	reg [15:0] rd_input_time_counter;
	reg rd_input_transpose;
	reg signed [15:0] rd_weight_ptr;
	reg [15:0] rd_weight_row_size;
	reg [15:0] rd_weight_col_size;
	reg [15:0] rd_weight_time_counter;
	reg rd_weight_transpose;
	reg [15:0] rd_weight_skip_size;
	reg [15:0] rd_bias_ptr;
	reg [15:0] rd_bias_row_size;
	reg [15:0] rd_bias_col_size;
	reg [15:0] rd_bias_time_counter;
	reg [15:0] rd_Y_ptr;
	reg [15:0] rd_Y_row_size;
	reg [15:0] rd_Y_col_size;
	reg [15:0] rd_Y_time_counter;
	reg [15:0] rd_H_ptr;
	reg [15:0] rd_H_row_size;
	reg [15:0] rd_H_col_size;
	reg [15:0] rd_H_time_counter;
	reg [15:0] rd_grad_bias_ptr;
	reg [15:0] rd_grad_bias_row_size;
	reg [15:0] rd_grad_bias_col_size;
	reg [15:0] rd_grad_bias_time_counter;
	reg [15:0] rd_grad_weight_ptr;
	reg [15:0] rd_grad_weight_row_size;
	reg [15:0] rd_grad_weight_col_size;
	reg [15:0] rd_grad_weight_time_counter;
	reg [15:0] value_old_in [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg grad_descent_valid_in [0:SYSTOLIC_ARRAY_WIDTH - 1];
	wire [15:0] value_updated_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	wire grad_descent_done_out [0:SYSTOLIC_ARRAY_WIDTH - 1];
	reg [15:0] grad_descent_ptr;
	reg grad_bias_or_weight;
	genvar _gv_i_1;
	generate
		for (_gv_i_1 = 0; _gv_i_1 < SYSTOLIC_ARRAY_WIDTH; _gv_i_1 = _gv_i_1 + 1) begin : gradient_descent_gen
			localparam i = _gv_i_1;
			gradient_descent gradient_descent_inst(
				.clk(clk),
				.rst(rst),
				.lr_in(learning_rate_in),
				.grad_in(ub_wr_data_in[((SYSTOLIC_ARRAY_WIDTH - 1) - i) * 16+:16]),
				.value_old_in(value_old_in[i]),
				.grad_descent_valid_in(grad_descent_valid_in[i]),
				.grad_bias_or_weight(grad_bias_or_weight),
				.value_updated_out(value_updated_out[i]),
				.grad_descent_done_out(grad_descent_done_out[i])
			);
		end
	endgenerate
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
	always @(*) begin
		if (_sv2v_0)
			;
		if (ub_rd_start_in)
			case (ub_ptr_select)
				0: begin
					rd_input_transpose = ub_rd_transpose;
					rd_input_ptr = ub_rd_addr_in;
					if (ub_rd_transpose) begin
						rd_input_row_size = ub_rd_col_size;
						rd_input_col_size = ub_rd_row_size;
					end
					else begin
						rd_input_row_size = ub_rd_row_size;
						rd_input_col_size = ub_rd_col_size;
					end
					rd_input_time_counter = 1'sb0;
				end
				1: begin
					rd_weight_transpose = ub_rd_transpose;
					if (ub_rd_transpose) begin
						rd_weight_row_size = ub_rd_col_size;
						rd_weight_col_size = ub_rd_row_size;
						rd_weight_ptr = (ub_rd_addr_in + ub_rd_col_size) - 1;
						ub_rd_col_size_out = ub_rd_row_size;
					end
					else begin
						rd_weight_row_size = ub_rd_row_size;
						rd_weight_col_size = ub_rd_col_size;
						rd_weight_ptr = (ub_rd_addr_in + (ub_rd_row_size * ub_rd_col_size)) - ub_rd_col_size;
						ub_rd_col_size_out = ub_rd_col_size;
					end
					rd_weight_skip_size = ub_rd_col_size + 1;
					rd_weight_time_counter = 1'sb0;
					ub_rd_col_size_valid_out = 1'b1;
				end
				2: begin
					rd_bias_ptr = ub_rd_addr_in;
					rd_bias_row_size = ub_rd_row_size;
					rd_bias_col_size = ub_rd_col_size;
					rd_bias_time_counter = 1'sb0;
				end
				3: begin
					rd_Y_ptr = ub_rd_addr_in;
					rd_Y_row_size = ub_rd_row_size;
					rd_Y_col_size = ub_rd_col_size;
					rd_Y_time_counter = 1'sb0;
				end
				4: begin
					rd_H_ptr = ub_rd_addr_in;
					rd_H_row_size = ub_rd_row_size;
					rd_H_col_size = ub_rd_col_size;
					rd_H_time_counter = 1'sb0;
				end
				5: begin
					rd_grad_bias_ptr = ub_rd_addr_in;
					rd_grad_bias_row_size = ub_rd_row_size;
					rd_grad_bias_col_size = ub_rd_col_size;
					rd_grad_bias_time_counter = 1'sb0;
					grad_bias_or_weight = 1'b0;
					grad_descent_ptr = ub_rd_addr_in;
				end
				6: begin
					rd_grad_weight_ptr = ub_rd_addr_in;
					rd_grad_weight_row_size = ub_rd_row_size;
					rd_grad_weight_col_size = ub_rd_col_size;
					rd_grad_weight_time_counter = 1'sb0;
					grad_bias_or_weight = 1'b1;
					grad_descent_ptr = ub_rd_addr_in;
				end
			endcase
		else begin
			ub_rd_col_size_out = 0;
			ub_rd_col_size_valid_out = 1'b0;
		end
	end
	always @(*) begin
		if (_sv2v_0)
			;
		if ((rd_grad_bias_time_counter < (rd_grad_bias_row_size + rd_grad_bias_col_size)) || (rd_grad_weight_time_counter < (rd_grad_weight_row_size + rd_grad_weight_col_size))) begin : sv2v_autoblock_1
			reg signed [31:0] i;
			for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
				grad_descent_valid_in[i] = ub_wr_valid_in[i];
		end
		else begin : sv2v_autoblock_2
			reg signed [31:0] i;
			for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
				grad_descent_valid_in[i] = 1'b0;
		end
	end
	always @(posedge clk or posedge rst) begin
		begin : sv2v_autoblock_3
			reg signed [31:0] i;
			for (i = 0; i < UNIFIED_BUFFER_WIDTH; i = i + 1)
				$dumpvars(0, ub_memory[i]);
		end
		begin : sv2v_autoblock_4
			reg signed [31:0] i;
			for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
				begin
					$dumpvars(0, ub_wr_data_in[((SYSTOLIC_ARRAY_WIDTH - 1) - i) * 16+:16]);
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
		end
		if (rst) begin
			begin : sv2v_autoblock_5
				reg signed [31:0] i;
				for (i = 0; i < UNIFIED_BUFFER_WIDTH; i = i + 1)
					ub_memory[i] <= 1'sb0;
			end
			begin : sv2v_autoblock_6
				reg signed [31:0] i;
				for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
					begin
						ub_rd_input_data_out[i] <= 1'sb0;
						ub_rd_input_valid_out[i] <= 1'sb0;
						ub_rd_weight_data_out[i] <= 1'sb0;
						ub_rd_weight_valid_out[i] <= 1'sb0;
						ub_rd_bias_data_out[i] <= 1'sb0;
						ub_rd_Y_data_out[i] <= 1'sb0;
						ub_rd_H_data_out[i] <= 1'sb0;
						value_old_in[i] <= 1'sb0;
						grad_descent_valid_in[i] <= 1'sb0;
					end
			end
			wr_ptr <= 1'sb0;
			rd_input_ptr <= 1'sb0;
			rd_input_row_size <= 1'sb0;
			rd_input_col_size <= 1'sb0;
			rd_input_time_counter <= 1'sb0;
			rd_input_transpose <= 1'sb0;
			rd_weight_ptr <= 1'sb0;
			rd_weight_row_size <= 1'sb0;
			rd_weight_col_size <= 1'sb0;
			rd_weight_time_counter <= 1'sb0;
			rd_weight_transpose <= 1'sb0;
			rd_bias_ptr <= 1'sb0;
			rd_bias_row_size <= 1'sb0;
			rd_bias_col_size <= 1'sb0;
			rd_bias_time_counter <= 1'sb0;
			rd_Y_ptr <= 1'sb0;
			rd_Y_row_size <= 1'sb0;
			rd_Y_col_size <= 1'sb0;
			rd_Y_time_counter <= 1'sb0;
			rd_H_ptr <= 1'sb0;
			rd_H_row_size <= 1'sb0;
			rd_H_col_size <= 1'sb0;
			rd_H_time_counter <= 1'sb0;
			rd_grad_bias_ptr <= 1'sb0;
			rd_grad_bias_row_size <= 1'sb0;
			rd_grad_bias_col_size <= 1'sb0;
			rd_grad_bias_time_counter <= 1'sb0;
			rd_grad_weight_ptr <= 1'sb0;
			rd_grad_weight_row_size <= 1'sb0;
			rd_grad_weight_col_size <= 1'sb0;
			rd_grad_weight_time_counter <= 1'sb0;
		end
		else begin
			begin : sv2v_autoblock_7
				reg signed [31:0] i;
				for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
					if (ub_wr_valid_in[i]) begin
						ub_memory[wr_ptr] <= ub_wr_data_in[((SYSTOLIC_ARRAY_WIDTH - 1) - i) * 16+:16];
						wr_ptr = wr_ptr + 1;
					end
					else if (ub_wr_host_valid_in[i]) begin
						ub_memory[wr_ptr] <= ub_wr_host_data_in[((SYSTOLIC_ARRAY_WIDTH - 1) - i) * 16+:16];
						wr_ptr = wr_ptr + 1;
					end
			end
			if (grad_bias_or_weight) begin : sv2v_autoblock_8
				reg signed [31:0] i;
				for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
					if (grad_descent_done_out[i]) begin
						ub_memory[grad_descent_ptr] <= value_updated_out[i];
						grad_descent_ptr = grad_descent_ptr + 1;
					end
			end
			else begin : sv2v_autoblock_9
				reg signed [31:0] i;
				for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
					if (grad_descent_done_out[i])
						ub_memory[grad_descent_ptr + i] <= value_updated_out[i];
			end
			if ((rd_input_time_counter + 1) < (rd_input_row_size + rd_input_col_size)) begin
				if (rd_input_transpose) begin : sv2v_autoblock_10
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						if (((rd_input_time_counter >= i) && (rd_input_time_counter < (rd_input_row_size + i))) && (i < rd_input_col_size)) begin
							ub_rd_input_valid_out[i] <= 1'b1;
							ub_rd_input_data_out[i] <= ub_memory[rd_input_ptr];
							rd_input_ptr = rd_input_ptr + 1;
						end
						else begin
							ub_rd_input_valid_out[i] <= 1'b0;
							ub_rd_input_data_out[i] <= 1'sb0;
						end
				end
				else begin : sv2v_autoblock_11
					reg signed [31:0] i;
					for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
						if (((rd_input_time_counter >= i) && (rd_input_time_counter < (rd_input_row_size + i))) && (i < rd_input_col_size)) begin
							ub_rd_input_valid_out[i] <= 1'b1;
							ub_rd_input_data_out[i] <= ub_memory[rd_input_ptr];
							rd_input_ptr = rd_input_ptr + 1;
						end
						else begin
							ub_rd_input_valid_out[i] <= 1'b0;
							ub_rd_input_data_out[i] <= 1'sb0;
						end
				end
				rd_input_time_counter <= rd_input_time_counter + 1;
			end
			else begin
				rd_input_ptr <= 0;
				rd_input_row_size <= 0;
				rd_input_col_size <= 0;
				rd_input_time_counter <= 1'sb0;
				begin : sv2v_autoblock_12
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						begin
							ub_rd_input_valid_out[i] <= 1'b0;
							ub_rd_input_data_out[i] <= 1'sb0;
						end
				end
			end
			if ((rd_weight_time_counter + 1) < (rd_weight_row_size + rd_weight_col_size)) begin
				if (rd_weight_transpose) begin
					begin : sv2v_autoblock_13
						reg signed [31:0] i;
						for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
							if (((rd_weight_time_counter >= i) && (rd_weight_time_counter < (rd_weight_row_size + i))) && (i < rd_weight_col_size)) begin
								ub_rd_weight_valid_out[i] <= 1'b1;
								ub_rd_weight_data_out[i] <= ub_memory[rd_weight_ptr];
								rd_weight_ptr = rd_weight_ptr + rd_weight_skip_size;
							end
							else begin
								ub_rd_weight_valid_out[i] <= 0;
								ub_rd_weight_data_out[i] <= 1'sb0;
							end
					end
					rd_weight_ptr = (rd_weight_ptr - rd_weight_skip_size) - 1;
				end
				else begin
					begin : sv2v_autoblock_14
						reg signed [31:0] i;
						for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
							if (((rd_weight_time_counter >= i) && (rd_weight_time_counter < (rd_weight_row_size + i))) && (i < rd_weight_col_size)) begin
								ub_rd_weight_valid_out[i] <= 1'b1;
								ub_rd_weight_data_out[i] <= ub_memory[rd_weight_ptr];
								rd_weight_ptr = rd_weight_ptr - rd_weight_skip_size;
							end
							else begin
								ub_rd_weight_valid_out[i] <= 0;
								ub_rd_weight_data_out[i] <= 1'sb0;
							end
					end
					rd_weight_ptr = (rd_weight_ptr + rd_weight_skip_size) + 1;
				end
				rd_weight_time_counter <= rd_weight_time_counter + 1;
			end
			else begin
				rd_weight_ptr <= 0;
				rd_weight_row_size <= 0;
				rd_weight_col_size <= 0;
				rd_weight_time_counter <= 1'sb0;
				begin : sv2v_autoblock_15
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						begin
							ub_rd_weight_valid_out[i] <= 0;
							ub_rd_weight_data_out[i] <= 1'sb0;
						end
				end
			end
			if ((rd_bias_time_counter + 1) < (rd_bias_row_size + rd_bias_col_size)) begin
				begin : sv2v_autoblock_16
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						if (((rd_bias_time_counter >= i) && (rd_bias_time_counter < (rd_bias_row_size + i))) && (i < rd_bias_col_size))
							ub_rd_bias_data_out[i] <= ub_memory[rd_bias_ptr + i];
						else
							ub_rd_bias_data_out[i] <= 1'sb0;
				end
				rd_bias_time_counter <= rd_bias_time_counter + 1;
			end
			else begin
				rd_bias_ptr <= 0;
				rd_bias_row_size <= 0;
				rd_bias_col_size <= 0;
				rd_bias_time_counter <= 1'sb0;
				begin : sv2v_autoblock_17
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						ub_rd_bias_data_out[i] <= 1'sb0;
				end
			end
			if ((rd_Y_time_counter + 1) < (rd_Y_row_size + rd_Y_col_size)) begin
				begin : sv2v_autoblock_18
					reg signed [31:0] i;
					for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
						if (((rd_Y_time_counter >= i) && (rd_Y_time_counter < (rd_Y_row_size + i))) && (i < rd_Y_col_size)) begin
							ub_rd_Y_data_out[i] <= ub_memory[rd_Y_ptr];
							rd_Y_ptr = rd_Y_ptr + 1;
						end
						else
							ub_rd_Y_data_out[i] <= 1'sb0;
				end
				rd_Y_time_counter <= rd_Y_time_counter + 1;
			end
			else begin
				rd_Y_ptr <= 0;
				rd_Y_row_size <= 0;
				rd_Y_col_size <= 0;
				rd_Y_time_counter <= 1'sb0;
				begin : sv2v_autoblock_19
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						ub_rd_Y_data_out[i] <= 1'sb0;
				end
			end
			if ((rd_H_time_counter + 1) < (rd_H_row_size + rd_H_col_size)) begin
				begin : sv2v_autoblock_20
					reg signed [31:0] i;
					for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
						if (((rd_H_time_counter >= i) && (rd_H_time_counter < (rd_H_row_size + i))) && (i < rd_H_col_size)) begin
							ub_rd_H_data_out[i] <= ub_memory[rd_H_ptr];
							rd_H_ptr = rd_H_ptr + 1;
						end
						else
							ub_rd_H_data_out[i] <= 1'sb0;
				end
				rd_H_time_counter <= rd_H_time_counter + 1;
			end
			else begin
				rd_H_ptr <= 0;
				rd_H_row_size <= 0;
				rd_H_col_size <= 0;
				rd_H_time_counter <= 1'sb0;
				begin : sv2v_autoblock_21
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						ub_rd_H_data_out[i] <= 1'sb0;
				end
			end
			if ((rd_grad_bias_time_counter + 1) < (rd_grad_bias_row_size + rd_grad_bias_col_size)) begin
				begin : sv2v_autoblock_22
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						if (((rd_grad_bias_time_counter >= i) && (rd_grad_bias_time_counter < (rd_grad_bias_row_size + i))) && (i < rd_grad_bias_col_size))
							value_old_in[i] <= ub_memory[rd_grad_bias_ptr + i];
						else
							value_old_in[i] <= 1'sb0;
				end
				rd_grad_bias_time_counter <= rd_grad_bias_time_counter + 1;
			end
			else if ((rd_grad_weight_time_counter + 1) < (rd_grad_weight_row_size + rd_grad_weight_col_size)) begin
				begin : sv2v_autoblock_23
					reg signed [31:0] i;
					for (i = SYSTOLIC_ARRAY_WIDTH - 1; i >= 0; i = i - 1)
						if (((rd_grad_weight_time_counter >= i) && (rd_grad_weight_time_counter < (rd_grad_weight_row_size + i))) && (i < rd_grad_weight_col_size)) begin
							value_old_in[i] <= ub_memory[rd_grad_weight_ptr];
							rd_grad_weight_ptr = rd_grad_weight_ptr + 1;
						end
						else
							value_old_in[i] <= 1'sb0;
				end
				rd_grad_weight_time_counter <= rd_grad_weight_time_counter + 1;
			end
			else begin
				rd_grad_bias_ptr <= 0;
				rd_grad_bias_row_size <= 0;
				rd_grad_bias_col_size <= 0;
				rd_grad_bias_time_counter <= 1'sb0;
				rd_grad_weight_ptr <= 0;
				rd_grad_weight_row_size <= 0;
				rd_grad_weight_col_size <= 0;
				rd_grad_weight_time_counter <= 1'sb0;
				begin : sv2v_autoblock_24
					reg signed [31:0] i;
					for (i = 0; i < SYSTOLIC_ARRAY_WIDTH; i = i + 1)
						value_old_in[i] <= 1'sb0;
				end
			end
		end
	end
	initial _sv2v_0 = 0;
endmodule
module vpu (
	clk,
	rst,
	vpu_data_pathway,
	vpu_data_in_1,
	vpu_data_in_2,
	vpu_valid_in_1,
	vpu_valid_in_2,
	bias_scalar_in_1,
	bias_scalar_in_2,
	lr_leak_factor_in,
	Y_in_1,
	Y_in_2,
	inv_batch_size_times_two_in,
	H_in_1,
	H_in_2,
	vpu_data_out_1,
	vpu_data_out_2,
	vpu_valid_out_1,
	vpu_valid_out_2
);
	input wire clk;
	input wire rst;
	input wire [3:0] vpu_data_pathway;
	input wire signed [15:0] vpu_data_in_1;
	input wire signed [15:0] vpu_data_in_2;
	input wire vpu_valid_in_1;
	input wire vpu_valid_in_2;
	input wire signed [15:0] bias_scalar_in_1;
	input wire signed [15:0] bias_scalar_in_2;
	input wire signed [15:0] lr_leak_factor_in;
	input wire signed [15:0] Y_in_1;
	input wire signed [15:0] Y_in_2;
	input wire signed [15:0] inv_batch_size_times_two_in;
	input wire signed [15:0] H_in_1;
	input wire signed [15:0] H_in_2;
	output reg signed [15:0] vpu_data_out_1;
	output reg signed [15:0] vpu_data_out_2;
	output reg vpu_valid_out_1;
	output reg vpu_valid_out_2;
	reg [15:0] bias_data_1_in;
	reg bias_valid_1_in;
	reg [15:0] bias_data_2_in;
	reg bias_valid_2_in;
	wire [15:0] bias_z_data_out_1;
	wire bias_valid_1_out;
	wire [15:0] bias_z_data_out_2;
	wire bias_valid_2_out;
	reg [15:0] b_to_lr_data_in_1;
	reg b_to_lr_valid_in_1;
	reg [15:0] b_to_lr_data_in_2;
	reg b_to_lr_valid_in_2;
	reg [15:0] lr_data_1_in;
	reg lr_valid_1_in;
	reg [15:0] lr_data_2_in;
	reg lr_valid_2_in;
	wire [15:0] lr_data_1_out;
	wire lr_valid_1_out;
	wire [15:0] lr_data_2_out;
	wire lr_valid_2_out;
	reg [15:0] lr_to_loss_data_in_1;
	reg lr_to_loss_valid_in_1;
	reg [15:0] lr_to_loss_data_in_2;
	reg lr_to_loss_valid_in_2;
	reg [15:0] loss_data_1_in;
	reg loss_valid_1_in;
	reg [15:0] loss_data_2_in;
	reg loss_valid_2_in;
	wire [15:0] loss_data_1_out;
	wire loss_valid_1_out;
	wire [15:0] loss_data_2_out;
	wire loss_valid_2_out;
	reg [15:0] loss_to_lrd_data_in_1;
	reg loss_to_lrd_valid_in_1;
	reg [15:0] loss_to_lrd_data_in_2;
	reg loss_to_lrd_valid_in_2;
	reg [15:0] lr_d_data_1_in;
	reg lr_d_valid_1_in;
	reg [15:0] lr_d_data_2_in;
	reg lr_d_valid_2_in;
	wire [15:0] lr_d_data_1_out;
	wire lr_d_valid_1_out;
	wire [15:0] lr_d_data_2_out;
	wire lr_d_valid_2_out;
	reg [15:0] lr_d_H_in_1;
	reg [15:0] lr_d_H_in_2;
	reg [15:0] last_H_data_1_in;
	reg [15:0] last_H_data_2_in;
	reg [15:0] last_H_data_1_out;
	reg [15:0] last_H_data_2_out;
	bias_parent bias_parent_inst(
		.clk(clk),
		.rst(rst),
		.bias_sys_data_in_1(bias_data_1_in),
		.bias_sys_data_in_2(bias_data_2_in),
		.bias_sys_valid_in_1(bias_valid_1_in),
		.bias_sys_valid_in_2(bias_valid_2_in),
		.bias_scalar_in_1(bias_scalar_in_1),
		.bias_scalar_in_2(bias_scalar_in_2),
		.bias_Z_valid_out_1(bias_valid_1_out),
		.bias_Z_valid_out_2(bias_valid_2_out),
		.bias_z_data_out_1(bias_z_data_out_1),
		.bias_z_data_out_2(bias_z_data_out_2)
	);
	leaky_relu_parent leaky_relu_parent_inst(
		.clk(clk),
		.rst(rst),
		.lr_data_1_in(lr_data_1_in),
		.lr_data_2_in(lr_data_2_in),
		.lr_valid_1_in(lr_valid_1_in),
		.lr_valid_2_in(lr_valid_2_in),
		.lr_leak_factor_in(lr_leak_factor_in),
		.lr_data_1_out(lr_data_1_out),
		.lr_data_2_out(lr_data_2_out),
		.lr_valid_1_out(lr_valid_1_out),
		.lr_valid_2_out(lr_valid_2_out)
	);
	loss_parent loss_parent_inst(
		.clk(clk),
		.rst(rst),
		.H_1_in(loss_data_1_in),
		.H_2_in(loss_data_2_in),
		.valid_1_in(loss_valid_1_in),
		.valid_2_in(loss_valid_2_in),
		.Y_1_in(Y_in_1),
		.Y_2_in(Y_in_2),
		.inv_batch_size_times_two_in(inv_batch_size_times_two_in),
		.gradient_1_out(loss_data_1_out),
		.gradient_2_out(loss_data_2_out),
		.valid_1_out(loss_valid_1_out),
		.valid_2_out(loss_valid_2_out)
	);
	leaky_relu_derivative_parent leaky_relu_derivative_parent_inst(
		.clk(clk),
		.rst(rst),
		.lr_d_data_1_in(lr_d_data_1_in),
		.lr_d_data_2_in(lr_d_data_2_in),
		.lr_d_valid_1_in(lr_d_valid_1_in),
		.lr_d_valid_2_in(lr_d_valid_2_in),
		.lr_d_H_1_in(lr_d_H_in_1),
		.lr_d_H_2_in(lr_d_H_in_2),
		.lr_leak_factor_in(lr_leak_factor_in),
		.lr_d_data_1_out(lr_d_data_1_out),
		.lr_d_data_2_out(lr_d_data_2_out),
		.lr_d_valid_1_out(lr_d_valid_1_out),
		.lr_d_valid_2_out(lr_d_valid_2_out)
	);
	always @(*)
		if (rst) begin
			vpu_data_out_1 = 16'b0000000000000000;
			vpu_data_out_2 = 16'b0000000000000000;
			vpu_valid_out_1 = 1'b0;
			vpu_valid_out_2 = 1'b0;
			bias_data_1_in = 16'b0000000000000000;
			bias_data_2_in = 16'b0000000000000000;
			bias_valid_1_in = 1'b0;
			bias_valid_2_in = 1'b0;
			lr_data_1_in = 16'b0000000000000000;
			lr_data_2_in = 16'b0000000000000000;
			lr_valid_1_in = 1'b0;
			lr_valid_2_in = 1'b0;
			loss_data_1_in = 16'b0000000000000000;
			loss_data_2_in = 16'b0000000000000000;
			loss_valid_1_in = 1'b0;
			loss_valid_2_in = 1'b0;
			lr_d_data_1_in = 16'b0000000000000000;
			lr_d_data_2_in = 16'b0000000000000000;
			lr_d_valid_1_in = 1'b0;
			lr_d_valid_2_in = 1'b0;
		end
		else begin
			if (vpu_data_pathway[3]) begin
				bias_data_1_in = vpu_data_in_1;
				bias_data_2_in = vpu_data_in_2;
				bias_valid_1_in = vpu_valid_in_1;
				bias_valid_2_in = vpu_valid_in_2;
				b_to_lr_data_in_1 = bias_z_data_out_1;
				b_to_lr_data_in_2 = bias_z_data_out_2;
				b_to_lr_valid_in_1 = bias_valid_1_out;
				b_to_lr_valid_in_2 = bias_valid_2_out;
			end
			else begin
				bias_data_1_in = 16'b0000000000000000;
				bias_data_2_in = 16'b0000000000000000;
				bias_valid_1_in = 1'b0;
				bias_valid_2_in = 1'b0;
				b_to_lr_data_in_1 = vpu_data_in_1;
				b_to_lr_data_in_2 = vpu_data_in_2;
				b_to_lr_valid_in_1 = vpu_valid_in_1;
				b_to_lr_valid_in_2 = vpu_valid_in_2;
			end
			if (vpu_data_pathway[2]) begin
				lr_data_1_in = b_to_lr_data_in_1;
				lr_data_2_in = b_to_lr_data_in_2;
				lr_valid_1_in = b_to_lr_valid_in_1;
				lr_valid_2_in = b_to_lr_valid_in_2;
				lr_to_loss_data_in_1 = lr_data_1_out;
				lr_to_loss_data_in_2 = lr_data_2_out;
				lr_to_loss_valid_in_1 = lr_valid_1_out;
				lr_to_loss_valid_in_2 = lr_valid_2_out;
			end
			else begin
				lr_data_1_in = 16'b0000000000000000;
				lr_data_2_in = 16'b0000000000000000;
				lr_valid_1_in = 1'b0;
				lr_valid_2_in = 1'b0;
				lr_to_loss_data_in_1 = b_to_lr_data_in_1;
				lr_to_loss_data_in_2 = b_to_lr_data_in_2;
				lr_to_loss_valid_in_1 = b_to_lr_valid_in_1;
				lr_to_loss_valid_in_2 = b_to_lr_valid_in_2;
			end
			if (vpu_data_pathway[1]) begin
				loss_data_1_in = lr_to_loss_data_in_1;
				loss_data_2_in = lr_to_loss_data_in_2;
				loss_valid_1_in = lr_to_loss_valid_in_1;
				loss_valid_2_in = lr_to_loss_valid_in_2;
				loss_to_lrd_data_in_1 = loss_data_1_out;
				loss_to_lrd_data_in_2 = loss_data_2_out;
				loss_to_lrd_valid_in_1 = loss_valid_1_out;
				loss_to_lrd_valid_in_2 = loss_valid_2_out;
				last_H_data_1_in = lr_data_1_out;
				last_H_data_2_in = lr_data_2_out;
				lr_d_H_in_1 = last_H_data_1_out;
				lr_d_H_in_2 = last_H_data_2_out;
			end
			else begin
				loss_data_1_in = 16'b0000000000000000;
				loss_data_2_in = 16'b0000000000000000;
				loss_valid_1_in = 1'b0;
				loss_valid_2_in = 1'b0;
				loss_to_lrd_data_in_1 = lr_to_loss_data_in_1;
				loss_to_lrd_data_in_2 = lr_to_loss_data_in_2;
				loss_to_lrd_valid_in_1 = lr_to_loss_valid_in_1;
				loss_to_lrd_valid_in_2 = lr_to_loss_valid_in_2;
				lr_d_H_in_1 = H_in_1;
				lr_d_H_in_2 = H_in_2;
			end
			if (vpu_data_pathway[0]) begin
				lr_d_data_1_in = loss_to_lrd_data_in_1;
				lr_d_data_2_in = loss_to_lrd_data_in_2;
				lr_d_valid_1_in = loss_to_lrd_valid_in_1;
				lr_d_valid_2_in = loss_to_lrd_valid_in_2;
				vpu_data_out_1 = lr_d_data_1_out;
				vpu_data_out_2 = lr_d_data_2_out;
				vpu_valid_out_1 = lr_d_valid_1_out;
				vpu_valid_out_2 = lr_d_valid_2_out;
			end
			else begin
				lr_d_data_1_in = loss_to_lrd_data_in_1;
				lr_d_data_2_in = loss_to_lrd_data_in_2;
				lr_d_valid_1_in = loss_to_lrd_valid_in_1;
				lr_d_valid_2_in = loss_to_lrd_valid_in_2;
				vpu_data_out_1 = loss_to_lrd_data_in_1;
				vpu_data_out_2 = loss_to_lrd_data_in_2;
				vpu_valid_out_1 = loss_to_lrd_valid_in_1;
				vpu_valid_out_2 = loss_to_lrd_valid_in_2;
			end
		end
	always @(posedge clk or posedge rst)
		if (rst) begin
			last_H_data_1_in <= 0;
			last_H_data_2_in <= 0;
			last_H_data_1_out <= 0;
			last_H_data_2_out <= 0;
		end
		else if (vpu_data_pathway[1]) begin
			last_H_data_1_out <= last_H_data_1_in;
			last_H_data_2_out <= last_H_data_2_in;
		end
		else begin
			last_H_data_1_out <= 0;
			last_H_data_2_out <= 0;
		end
endmodule
module tpu (
	clk,
	rst,
	ub_wr_host_data_in,
	ub_wr_host_valid_in,
	ub_rd_start_in,
	ub_rd_transpose,
	ub_ptr_select,
	ub_rd_addr_in,
	ub_rd_row_size,
	ub_rd_col_size,
	learning_rate_in,
	vpu_data_pathway,
	sys_switch_in,
	vpu_leak_factor_in,
	inv_batch_size_times_two_in
);
	parameter signed [31:0] SYSTOLIC_ARRAY_WIDTH = 2;
	input wire clk;
	input wire rst;
	input wire [(SYSTOLIC_ARRAY_WIDTH * 16) - 1:0] ub_wr_host_data_in;
	input wire [0:SYSTOLIC_ARRAY_WIDTH - 1] ub_wr_host_valid_in;
	input wire ub_rd_start_in;
	input wire ub_rd_transpose;
	input wire [8:0] ub_ptr_select;
	input wire [15:0] ub_rd_addr_in;
	input wire [15:0] ub_rd_row_size;
	input wire [15:0] ub_rd_col_size;
	input wire [15:0] learning_rate_in;
	input wire [3:0] vpu_data_pathway;
	input wire sys_switch_in;
	input wire [15:0] vpu_leak_factor_in;
	input wire [15:0] inv_batch_size_times_two_in;
	wire [(SYSTOLIC_ARRAY_WIDTH * 16) - 1:0] ub_wr_data_in;
	wire [0:SYSTOLIC_ARRAY_WIDTH - 1] ub_wr_valid_in;
	wire [15:0] ub_rd_col_size_out;
	wire ub_rd_col_size_valid_out;
	wire [15:0] ub_rd_input_data_out_0;
	wire [15:0] ub_rd_input_data_out_1;
	wire ub_rd_input_valid_out_0;
	wire ub_rd_input_valid_out_1;
	wire [15:0] ub_rd_weight_data_out_0;
	wire [15:0] ub_rd_weight_data_out_1;
	wire ub_rd_weight_valid_out_0;
	wire ub_rd_weight_valid_out_1;
	wire [15:0] ub_rd_bias_data_out_0;
	wire [15:0] ub_rd_bias_data_out_1;
	wire [15:0] ub_rd_Y_data_out_0;
	wire [15:0] ub_rd_Y_data_out_1;
	wire [15:0] ub_rd_H_data_out_0;
	wire [15:0] ub_rd_H_data_out_1;
	wire [15:0] sys_data_out_21;
	wire [15:0] sys_data_out_22;
	wire sys_valid_out_21;
	wire sys_valid_out_22;
	wire [15:0] vpu_data_out_1;
	wire [15:0] vpu_data_out_2;
	wire vpu_valid_out_1;
	wire vpu_valid_out_2;
	assign ub_wr_data_in[(SYSTOLIC_ARRAY_WIDTH - 1) * 16+:16] = vpu_data_out_1;
	assign ub_wr_data_in[(SYSTOLIC_ARRAY_WIDTH - 2) * 16+:16] = vpu_data_out_2;
	assign ub_wr_valid_in[0] = vpu_valid_out_1;
	assign ub_wr_valid_in[1] = vpu_valid_out_2;
	unified_buffer #(.SYSTOLIC_ARRAY_WIDTH(SYSTOLIC_ARRAY_WIDTH)) ub_inst(
		.clk(clk),
		.rst(rst),
		.ub_wr_data_in(ub_wr_data_in),
		.ub_wr_valid_in(ub_wr_valid_in),
		.ub_wr_host_data_in(ub_wr_host_data_in),
		.ub_wr_host_valid_in(ub_wr_host_valid_in),
		.ub_rd_start_in(ub_rd_start_in),
		.ub_rd_transpose(ub_rd_transpose),
		.ub_ptr_select(ub_ptr_select),
		.ub_rd_addr_in(ub_rd_addr_in),
		.ub_rd_row_size(ub_rd_row_size),
		.ub_rd_col_size(ub_rd_col_size),
		.learning_rate_in(learning_rate_in),
		.ub_rd_input_data_out_0(ub_rd_input_data_out_0),
		.ub_rd_input_data_out_1(ub_rd_input_data_out_1),
		.ub_rd_input_valid_out_0(ub_rd_input_valid_out_0),
		.ub_rd_input_valid_out_1(ub_rd_input_valid_out_1),
		.ub_rd_weight_data_out_0(ub_rd_weight_data_out_0),
		.ub_rd_weight_data_out_1(ub_rd_weight_data_out_1),
		.ub_rd_weight_valid_out_0(ub_rd_weight_valid_out_0),
		.ub_rd_weight_valid_out_1(ub_rd_weight_valid_out_1),
		.ub_rd_bias_data_out_0(ub_rd_bias_data_out_0),
		.ub_rd_bias_data_out_1(ub_rd_bias_data_out_1),
		.ub_rd_Y_data_out_0(ub_rd_Y_data_out_0),
		.ub_rd_Y_data_out_1(ub_rd_Y_data_out_1),
		.ub_rd_H_data_out_0(ub_rd_H_data_out_0),
		.ub_rd_H_data_out_1(ub_rd_H_data_out_1),
		.ub_rd_col_size_out(ub_rd_col_size_out),
		.ub_rd_col_size_valid_out(ub_rd_col_size_valid_out)
	);
	systolic systolic_inst(
		.clk(clk),
		.rst(rst),
		.sys_data_in_11(ub_rd_input_data_out_0),
		.sys_data_in_21(ub_rd_input_data_out_1),
		.sys_start(ub_rd_input_valid_out_0),
		.sys_data_out_21(sys_data_out_21),
		.sys_data_out_22(sys_data_out_22),
		.sys_valid_out_21(sys_valid_out_21),
		.sys_valid_out_22(sys_valid_out_22),
		.sys_weight_in_11(ub_rd_weight_data_out_0),
		.sys_weight_in_12(ub_rd_weight_data_out_1),
		.sys_accept_w_1(ub_rd_weight_valid_out_0),
		.sys_accept_w_2(ub_rd_weight_valid_out_1),
		.sys_switch_in(sys_switch_in),
		.ub_rd_col_size_in(ub_rd_col_size_out),
		.ub_rd_col_size_valid_in(ub_rd_col_size_valid_out)
	);
	vpu vpu_inst(
		.clk(clk),
		.rst(rst),
		.vpu_data_pathway(vpu_data_pathway),
		.vpu_data_in_1(sys_data_out_21),
		.vpu_data_in_2(sys_data_out_22),
		.vpu_valid_in_1(sys_valid_out_21),
		.vpu_valid_in_2(sys_valid_out_22),
		.bias_scalar_in_1(ub_rd_bias_data_out_0),
		.bias_scalar_in_2(ub_rd_bias_data_out_1),
		.lr_leak_factor_in(vpu_leak_factor_in),
		.Y_in_1(ub_rd_Y_data_out_0),
		.Y_in_2(ub_rd_Y_data_out_1),
		.inv_batch_size_times_two_in(inv_batch_size_times_two_in),
		.H_in_1(ub_rd_H_data_out_0),
		.H_in_2(ub_rd_H_data_out_1),
		.vpu_data_out_1(vpu_data_out_1),
		.vpu_data_out_2(vpu_data_out_2),
		.vpu_valid_out_1(vpu_valid_out_1),
		.vpu_valid_out_2(vpu_valid_out_2)
	);
endmodule
