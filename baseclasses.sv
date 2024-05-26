package pack1;

import uvm_pkg::*;
`include "uvm_macros.svh"


class my_sequence_item extends uvm_sequence_item;
	`uvm_object_utils(my_sequence_item)

function new (string name="my_sequence_item");
	super.new(name);
endfunction

//simple function in the sequence item//

function void print (string s);
	$display("%s",s);
endfunction

//Defining Signal and putting constraints on it //

rand bit Wr_enable;
rand bit Read_enable;
rand bit [31:0] data_in;
rand bit reset;
logic full;
logic empty;
logic [31:0] data_out;



  





constraint const1 {data_in[7:0] inside {[100:230]};} 
constraint const2 {data_in[15:8] inside {[200:255]};} 
constraint const3 {data_in[23:16] dist {[0:100]:=3,[100:200]:=6,[200:255]:=1};} 
constraint const8 {if (data_in[7:0] > 150) data_in[31:24] < 50; 
					else data_in[31:24] < 255;}
constraint const5 {Wr_enable dist {0:=3, 1:=7};}
constraint const6 {Read_enable dist {0:=7, 1:=3};}
constraint const7 {reset dist {1:=1, 0:=999};}
endclass


class my_sequence extends uvm_sequence;
	`uvm_object_utils(my_sequence)	

my_sequence_item sequence1;
my_sequence_item sequence2;

task pre_body;
	sequence1=my_sequence_item::type_id::create("sequence1");
	sequence2=my_sequence_item::type_id::create("sequence2");
endtask

task body;   /// here to cover states as much as possible we make elevators to move in opposite directions

	repeat(40)
	begin
	start_item(sequence1);
	void'(sequence1.randomize());
	finish_item(sequence1);

	start_item(sequence2);
	void'(sequence2.randomize());
	finish_item(sequence2);
	end
endtask




endclass


class my_driver  extends uvm_driver #(my_sequence_item);

`uvm_component_utils(my_driver)



my_sequence_item sequence1;
my_sequence_item sequence2;






function new (string name="my_driver",uvm_component parent = null);
	super.new(name,parent);
endfunction


virtual interface intf1.in_tb config_virtual;


function void build_phase (uvm_phase phase);
	if(!uvm_config_db#(virtual intf1.in_tb)::get(this,"","my_vif",config_virtual))
	`uvm_fatal(get_full_name(),"EEROR!")
	$display(config_virtual);

	super.build_phase(phase);
	$display("driver is built");
	sequence1=my_sequence_item::type_id::create("sequence1");
	sequence2=my_sequence_item::type_id::create("sequence2");
endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("driver is connected");
endfunction

//run phase methods
task run_phase(uvm_phase phase);
	super.run_phase(phase);
	
	forever begin
	seq_item_port.get_next_item(sequence1);
	//sending data to the DUT
	@(negedge config_virtual.cb) 
	begin
	config_virtual.cb.data_in <= sequence1.data_in;
	config_virtual.cb.Wr_enable <= sequence1.Wr_enable;
	config_virtual.cb.Read_enable <= sequence1.Read_enable;
	config_virtual.cb.reset <= sequence1.reset;

	end
	#1 seq_item_port.item_done();
	end

	forever begin
	seq_item_port.get_next_item(sequence2);
	//sending data to the DUT
	@(negedge config_virtual.cb)
	begin
	config_virtual.cb.data_in <= sequence1.data_in;
	config_virtual.cb.Wr_enable <= sequence1.Wr_enable;
	config_virtual.cb.Read_enable <= sequence1.Read_enable;
	config_virtual.cb.reset <= sequence1.reset;
	end
	#1 seq_item_port.item_done();
	end

	
endtask

endclass

class my_sequencer extends uvm_sequencer #(my_sequence_item);
`uvm_component_utils(my_sequencer)


function new (string name="my_sequencer",uvm_component parent = null);
	super.new(name,parent);
endfunction

function void build_phase (uvm_phase phase);
	super.build_phase(phase);
	$display("sequencer is built");
	
endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("sequencer is connected");
endfunction

//run phase methods
task run_phase(uvm_phase phase);
	super.run_phase(phase);
endtask

endclass

class my_monitor extends uvm_monitor;
`uvm_component_utils(my_monitor)
uvm_analysis_port #(my_sequence_item) my_analysis_port;

my_sequence_item sequence1;
my_sequence_item sequence2;


function new (string name="my_monitor",uvm_component parent = null);
	super.new(name,parent);
endfunction


virtual interface intf1.in_tb config_virtual;


function void build_phase (uvm_phase phase);
	if(!uvm_config_db#(virtual intf1.in_tb)::get(this,"","my_vif",config_virtual))
	`uvm_fatal(get_full_name(),"EEROR!")
	$display(config_virtual);

	super.build_phase(phase);
	$display("monitor is built");
	my_analysis_port=new("my_analysis_port",this);
	sequence1=my_sequence_item::type_id::create("sequence1");
	sequence2=my_sequence_item::type_id::create("sequence2");	
endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("monitor is connected");
endfunction

//run phase methods
task run_phase(uvm_phase phase);
	
	forever begin
		@(posedge config_virtual.cb)
		begin
		sequence1.full <= config_virtual.cb.full;
		sequence1.empty <= config_virtual.cb.empty;
		sequence1.data_out <= config_virtual.cb.data_out;



		/*sequence1.data_in <= config_virtual.cb.data_in;
		sequence1.Wr_enable <= config_virtual.cb.Wr_enable;
		sequence1.Read_enable <= config_virtual.cb.Read_enable;
		sequence1.reset <= config_virtual.cb.reset;*/
		
		$display("From monitor %d  %d  %d  ",config_virtual.cb.data_out,config_virtual.cb.empty,config_virtual.cb.full);
		end
	
		my_analysis_port.write(sequence1);
	
		end
endtask

endclass

class my_scoreboard extends uvm_scoreboard;
`uvm_component_utils(my_scoreboard)

uvm_analysis_export #(my_sequence_item) my_analysis_export;
uvm_tlm_analysis_fifo #(my_sequence_item) my_analysis_fifo;

my_sequence_item sequence1;

function new (string name="my_scoreboard",uvm_component parent = null);
	super.new(name,parent);
endfunction

function void build_phase (uvm_phase phase);
	super.build_phase(phase);
	$display("scoreboard is built");
	my_analysis_export=new("my_analysis_export",this);
	my_analysis_fifo=new("my_analysis_fifo",this);
endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("scoreboard is connected");
	my_analysis_export.connect(my_analysis_fifo.analysis_export);

endfunction

//run phase methods
task run_phase(uvm_phase phase);
	forever begin
	my_analysis_fifo.get_peek_export.get(sequence1);
	$display("from scoreboard %d",sequence1.full);
	$display("from scoreboard %d",sequence1.empty);
	$display("from scoreboard %d",sequence1.data_out);


	// HERE we could add compare function if we had an expected value file//
	end
endtask


function void write (my_sequence_item t);
	t.print("HELLO from scoreboard");
endfunction


endclass

class my_subscriber extends uvm_subscriber #(my_sequence_item);
`uvm_component_utils(my_subscriber)

uvm_analysis_imp #(my_sequence_item,my_subscriber) my_analysis_imp;



my_sequence_item sequence1;

//making a covergroup for all ranges


covergroup group1;

	coverpoint sequence1.full {bins bin_1[]={[0:1]};}
	coverpoint sequence1.empty {bins bin_1[]={[0:1]};}

endgroup



function new (string name="my_subscriber",uvm_component parent = null);
	super.new(name,parent);
	group1=new();
endfunction



function void write (my_sequence_item t);
	t.print("HI from subscriber");
	sequence1 = my_sequence_item::type_id::create("sequence1");
	$cast(sequence1,t);
	group1.sample();
	
endfunction

function void build_phase (uvm_phase phase);
	super.build_phase(phase);
	$display("subscriber is built");
	
	my_analysis_imp=new("my_analysis_imp",this);
endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("subscriber is connected");
endfunction

//run phase methods
task run_phase(uvm_phase phase);
	super.run_phase(phase);
endtask


endclass

class my_agent extends uvm_agent;
`uvm_component_utils(my_agent)
uvm_analysis_port #(my_sequence_item) my_analysis_port;

function new (string name="my_agent",uvm_component parent = null);
	super.new(name,parent);
endfunction

my_driver d1;
my_sequencer s1;
my_monitor m1;


virtual interface intf1.in_tb config_virtual;
virtual interface intf1.in_tb local_virtual;

function void build_phase (uvm_phase phase);
	if(!uvm_config_db#(virtual intf1.in_tb)::get(this,"","my_vif",config_virtual))
	`uvm_fatal(get_full_name(),"EEROR!")

	local_virtual=config_virtual;

	uvm_config_db#(virtual intf1.in_tb)::set(this,"d1","my_vif",local_virtual);
	uvm_config_db#(virtual intf1.in_tb)::set(this,"m1","my_vif",local_virtual);

	my_analysis_port=new("my_analysis_port",this);

	super.build_phase(phase);
	$display("agent is built");
	d1=my_driver::type_id::create("d1",this);
	s1=my_sequencer::type_id::create("s1",this);
	m1=my_monitor::type_id::create("m1",this);
endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("agent is connected");
	m1.my_analysis_port.connect(this.my_analysis_port);

	d1.seq_item_port.connect(s1.seq_item_export);	

endfunction

//run phase methods
task run_phase(uvm_phase phase);
	super.run_phase(phase);
endtask

endclass

class my_env extends uvm_env;
`uvm_component_utils(my_env)

function new (string name="my_env",uvm_component parent = null);
	super.new(name,parent);
endfunction

my_agent a1;
my_subscriber su1;
my_scoreboard sb1;


virtual interface intf1.in_tb config_virtual;
virtual interface intf1.in_tb local_virtual;

function void build_phase (uvm_phase phase);
	if(!uvm_config_db#(virtual intf1.in_tb)::get(this,"","my_vif",config_virtual))
	`uvm_fatal(get_full_name(),"EEROR!")

	local_virtual=config_virtual;

	su1=my_subscriber::type_id::create("su1",this);
	sb1=my_scoreboard::type_id::create("sb1",this);
	a1=my_agent::type_id::create("a1",this);

	uvm_config_db#(virtual intf1.in_tb)::set(this,"a1","my_vif",local_virtual);


	super.build_phase(phase);
	$display("Env is built");

endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("Env is connected");
	a1.my_analysis_port.connect(sb1.my_analysis_export);
	a1.my_analysis_port.connect(su1.my_analysis_imp);
endfunction

//run phase methods
task run_phase(uvm_phase phase);
	super.run_phase(phase);
endtask


endclass

class my_test extends uvm_test;
`uvm_component_utils(my_test)

function new (string name="my_test",uvm_component parent = null);
	super.new(name,parent);
endfunction

my_env e1;
my_sequence seq1;

virtual interface intf1.in_tb config_virtual;
virtual interface intf1.in_tb local_virtual;

function void build_phase (uvm_phase phase);
	if(!uvm_config_db#(virtual intf1.in_tb)::get(this,"","my_vif",config_virtual))
	`uvm_fatal(get_full_name(),"EEROR!")

	seq1=my_sequence::type_id::create("seq1");
	e1=my_env::type_id::create("e1",this);

	local_virtual=config_virtual;

	uvm_config_db#(virtual intf1.in_tb)::set(this,"e1","my_vif",local_virtual);

	super.build_phase(phase);
	$display("test is built");

endfunction

function void connect_phase (uvm_phase phase);
	super.connect_phase(phase);
	$display("test is connected");
endfunction

//run phase methods
task run_phase(uvm_phase phase);
	super.run_phase(phase);

	phase.raise_objection(this);
	seq1.start(e1.a1.s1);
	phase.drop_objection(this);
	
	phase.raise_objection(this);
	seq1.start(e1.a1.s1);
	phase.drop_objection(this);

endtask

endclass

endpackage

