module FIFO_Assertions #(parameter DATA_WIDTH = 8 ,parameter ADDR_WIDTH = 5)
                        (FIFO_intf.DUT  Assertion_FIFO_intf, input [ADDR_WIDTH -1:0] wr_ptr, input [ADDR_WIDTH -1:0] rd_ptr);


logic                   clk_ass;
logic                   reset_ass;
logic                   Wr_enable_ass;
logic [DATA_WIDTH -1:0] data_in_ass;
logic                   Read_enable_ass;

assign clk_ass         = Assertion_FIFO_intf.clk_intf;
assign reset_ass       = Assertion_FIFO_intf.reset_intf;
assign data_in_ass     = Assertion_FIFO_intf.data_in_intf;
assign Wr_enable_ass   = Assertion_FIFO_intf.Wr_enable_intf;
assign Read_enable_ass = Assertion_FIFO_intf.Read_enable_intf;

////////////////////////////////////////////////////////
//////////////// Property and Assertions ///////////////
////////////////////////////////////////////////////////

logic [ADDR_WIDTH -1:0] write_pointer = 0;
logic [ADDR_WIDTH -1:0] read_pointer = 0;

always @(posedge clk_ass or posedge reset_ass)
    begin
	    if (reset_ass) write_pointer = 0;
		
	    else if(Wr_enable_ass && !Assertion_FIFO_intf.full_intf)begin
	        write_pointer++;
		end
	end
	
always @(posedge clk_ass or posedge reset_ass)
    begin
	    if (reset_ass) read_pointer = 0;
		
	    else if(Read_enable_ass && !Assertion_FIFO_intf.empty_intf)begin
	        read_pointer++;
		end
	end	

/////////////// Assertion for incrementing write pointer ///////////////

property Increment_wr_ptr;
    @(posedge clk_ass) disable iff(reset_ass) (Wr_enable_ass && !Assertion_FIFO_intf.full_intf) |=> (wr_ptr == write_pointer);
endproperty

assert property (Increment_wr_ptr) else $display("Error in assertion where wr_ptr is %d and the actulal pointer is %d",wr_ptr,write_pointer);
cover property (Increment_wr_ptr);

//////////////// Assertion for incrementing read pointer ///////////////

property Increment_rd_ptr;
    @(posedge clk_ass) disable iff(reset_ass) (Read_enable_ass && !Assertion_FIFO_intf.empty_intf) |=> (rd_ptr == read_pointer);
endproperty

assert property (Increment_rd_ptr) else $display("Error in assertion where rd_ptr is %d and the actulal pointer is %d",rd_ptr,read_pointer);
cover property (Increment_rd_ptr);


assert property(@(posedge clk_ass) disable iff(reset_ass) (rd_ptr == 'd0 && wr_ptr == 'd31) |-> Assertion_FIFO_intf.full_intf);

////// This assertion is done and we discover a bug which is when rd_ptr equals 0 and 
////// wr_ptr equals 31 full flag didn't rise.

///// This bug leads to when we fill fifo and we didn't read any value, wr_ptr will be 
///// equal to rd_ptr and then empty flag wiil rise as full flag didn't rise. This is 
///// wrong as the fifo is not empty and empty flag is high.

endmodule