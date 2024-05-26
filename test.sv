//import test::*;


program automatic test(intf1.in_tb I0_in_tb);

initial begin
$display("Hello World");

test1();
end

task test1();
I0_in_tb.cb.rst<=1'b1;

@(I0_in_tb.cb)
I0_in_tb.cb.rst<=1'b0;
I0_in_tb.cb.request<=2'b01;


@(I0_in_tb.cb)
I0_in_tb.cb.rst<=1'b0;
I0_in_tb.cb.request<=2'b10;

@(I0_in_tb.cb)
I0_in_tb.cb.rst<=1'b0;
I0_in_tb.cb.request<=2'b00;

@(I0_in_tb.cb)
I0_in_tb.cb.rst<=1'b0;
I0_in_tb.cb.request<=2'b00;

endtask

endprogram
