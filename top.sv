

//creating interface between DUT & UVM Environment

interface intf1 (input clk);
logic reset;
logic Wr_enable;
logic Read_enable;
logic full;
logic empty;
logic [31:0] data_in;
logic [31:0] data_out;

clocking cb @(negedge clk);
default input #1 output #0;

output reset;
output Wr_enable;
output Read_enable;
output data_in;
input  data_out;
input full;
input empty;
endclocking

modport in_FIFO (input clk ,input reset,input Wr_enable, input Read_enable,input data_in , output full , output empty ,output data_out);
modport in_tb (clocking cb,input clk);



endinterface



module FIFO #(parameter
    ADDR_WIDTH           = 5,
    DATA_WIDTH           = 32,
    fifo_size                   =2**ADDR_WIDTH
  )(
	intf1.in_FIFO IO_in_fifo
  ); 
    reg  [DATA_WIDTH-1:0] FIFO  [fifo_size-1:0] ;
    reg [ADDR_WIDTH-1:0] write_ptr,read_ptr;
	reg[15:0] temp=0;		//represent old value of write pointer

    assign IO_in_fifo.empty   = ( write_ptr == read_ptr ) ? 1'b1 : 1'b0;
    assign IO_in_fifo.full    = ( read_ptr == (write_ptr+1) ) ? 1'b1 : 1'b0;
integer i;
    always @ (posedge IO_in_fifo.clk , posedge IO_in_fifo.reset) begin
        if(IO_in_fifo.reset) begin
         for(i=0;i<fifo_size;i=i+1) begin
            FIFO[i]<=0;
         end
         write_ptr <=0;
        end
  else if( IO_in_fifo.Wr_enable && ~IO_in_fifo.full) begin
            FIFO[write_ptr] <= IO_in_fifo.data_in;
              write_ptr <= write_ptr + 1;
		temp<=write_ptr;
        end

    end

    always @ (posedge IO_in_fifo.clk, posedge IO_in_fifo.reset) begin

        if(IO_in_fifo.reset) begin
            IO_in_fifo.data_out <= 0;
            read_ptr <= 0;
        end

        else if( IO_in_fifo.Read_enable && ~IO_in_fifo.empty) begin
            IO_in_fifo.data_out <= FIFO[read_ptr];
            read_ptr <= read_ptr + 1;
        end

    end


/////////////// Assertion for incrementing write pointer ///////////////

property Increment_wr_ptr;
    @(negedge IO_in_fifo.clk) disable iff(IO_in_fifo.reset) (IO_in_fifo.Wr_enable && !IO_in_fifo.full) |=> ((temp+1) == write_ptr);
endproperty

assert property (Increment_wr_ptr) else $display("Error in assertion where wr_ptr is %d and the actulal pointer is %d",temp,write_ptr);
cover property (Increment_wr_ptr);
//////////////////////////////////////////////////////////




endmodule






