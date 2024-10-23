module top_tb;
import uvm_pkg::*;
import pack1::*;

bit clk;

  // Clock generator
  initial
  begin	
    clk = 0;
    forever #5 clk = ~clk;
  end

intf1 in1(clk);

FIFO dut(.IO_in_fifo(in1.in_FIFO));






initial 
begin
in1.reset=1;
uvm_config_db #(virtual intf1.in_tb)::set(null,"uvm_test_top","my_vif",in1.in_tb);

run_test("my_test");
end


endmodule

