///////////////////////////////////////////////////////////////////////////
// Texas A&M University
// CSCE 616 Hardware Design Verification
// Created by  : Prof. Quinn and Saumil Gogri
///////////////////////////////////////////////////////////////////////////

interface htax_tx_interface (input clk, rst_n);

  import uvm_pkg::*;
  `include "uvm_macros.svh"

	parameter PORTS = `PORTS;
	parameter VC = `VC;
	parameter WIDTH = `WIDTH;
	
	logic [PORTS-1:0] tx_outport_req;
	logic [VC-1:0] 		tx_vc_req;
	logic [VC-1:0] 		tx_vc_gnt;
	logic [WIDTH-1:0]	tx_data;
	logic [VC-1:0]		tx_sot;
	logic							tx_eot;
	logic 						tx_release_gnt;

//TO DO : ASSERTIONS

   // --------------------------- 
   // tx_outport_req is one-hot 
   // --------------------------- 
   property tx_outport_req_one_hot;
      @(posedge clk) disable iff(!rst_n)
      (|tx_outport_req) |-> $onehot(tx_outport_req);
   endproperty

   assert_tx_outport_req_one_hot : assert property(tx_outport_req_one_hot)
   else
      $error("HTAX_TX_INF ERROR : tx_outport request is not one hot encoded");

   // ----------------------------------- 
   // no tx_outport_req without tx_vc_req
   // ----------------------------------- 
   
   property tx_outport_req_without_tx_vc_req;
      @(posedge clk) disable iff(!rst_n)
      ~(|tx_vc_req)  |-> (|tx_outport_req == 0);
   endproperty

   assert_tx_outport_req_without_tx_vc_req : assert property(tx_outport_req_without_tx_vc_req)
   else
      $error("HTAX_TX_INF ERROR : tx_outport_req without tx_vc_req");

   // ----------------------------------- 
   // no tx_vc_req without tx_outport_req
   // ----------------------------------- 

   property tx_vc_req_without_tx_outport_req;
      @(posedge clk) disable iff(!rst_n)
      ~(|tx_outport_req)  |-> (|tx_vc_req == 0);
   endproperty

   assert_tx_vc_req_without_tx_outport_req : assert property(tx_vc_req_without_tx_outport_req)
   else
      $error("HTAX_TX_INF ERROR : tx_vc_req without tx_outport_req");



   // ----------------------------------- 
   // tx_vc_gnt is subset of vc_request
   // ----------------------------------- 

   property tx_vc_gnt_subset_vc_request;
      @(posedge clk) disable iff(!rst_n)
      (|tx_vc_gnt)  |-> (tx_vc_req==tx_vc_gnt);
   endproperty

   assert_tx_vc_gnt_subset_vc_request : assert property(tx_vc_gnt_subset_vc_request)
   else
      $error("HTAX_TX_INF ERROR : tx_vc_gnt is not a subset of vc_request");



   // ------------------------------------ 
   // no tx_sot without previous tx_vc_gnt 
   // ------------------------------------ 

   property no_tx_sot_without_previous_tx_vc_gnt;
      @(posedge clk) disable iff(!rst_n)
      ~(|tx_vc_gnt) |-> ##[1:$] ~(tx_sot);
   endproperty

   assert_no_tx_sot_without_previous_tx_vc_gnt : assert property(no_tx_sot_without_previous_tx_vc_gnt)
   else
      $error("HTAX_TX_INF ERROR : tx_sot without previous tx_vc_gnt");



   // ------------------------------------ 
   // no tx_eot without previous tx_vc_gnt 
   // ------------------------------------ 

// Creating a ref_signal that will get asserted when tx_eot is one and gets deasserted when tx_vc_gnt gets 1.
//Now will check for the tx_eot signal when the ref_signal is being 1 and which will check for the above condition.
   
   logic ref_sig1;
   assign ref_sig1 = ~rst_n ? 1'b0 : (|tx_vc_gnt) ? 1'b0 : tx_eot ? 1'b1 : ref_sig1 ;
   property tx_eot_without_tx_vc_gnt;
      @(posedge clk) disable iff(!rst_n)
      ref_sig1  |=> ~(tx_eot);
   endproperty

   assert_tx_eot_without_tx_vc_gnt : assert property(tx_eot_without_tx_vc_gnt)
   else
      $error("HTAX_TX_INF ERROR : tx_eot without previous tx_vc_gnt");



   // ------------------------------------------- 
   // tx_eot is asserted for a single clock cycle 
   // ------------------------------------------- 

   property tx_eot_asserted_for_one_cycle;
      @(posedge clk) disable iff(!rst_n)
      (tx_eot)  |=> ~(tx_eot);
   endproperty

   assert_tx_eot_asserted_for_one_cycle : assert property(tx_eot_asserted_for_one_cycle)
   else
      $error("HTAX_TX_INF ERROR : tx_eot is not asserted for a single clock cycle");



   // ------------------------------------------------------------- 
   // tx_release_gnt for pkt(t) one clock cycle or same clock cycle with tx_eot of pkt(t)
   // ------------------------------------------------------------- 

   property tx_release_gnt_check_tx_eot;
      @(posedge clk) disable iff(!rst_n)
      (tx_release_gnt)  |-> ##[0:1] (tx_eot);
   endproperty

   assert_tx_release_gnt_check_tx_eot : assert property(tx_release_gnt_check_tx_eot)
   else
      $error("HTAX_TX_INF ERROR : tx_release_gnt for pkt(t) not in one clock cycle or same clock cycle with tx_eot of pkt(t)");


   // ------------------------------------------------------------- 
   // No tx_sot of p(t+1) without tx_eot for p(t)
   // ------------------------------------------------------------- 

// Creating a ref_signal that will get asserted when tx_sot is one and gets deasserted when tx_eot gets 1.
//Now will check for the tx_sot signal when the ref_signal is being 1 and which will check for the above condition.

   logic ref_sig;
   assign ref_sig = ~rst_n ? 1'b0 : (|tx_sot) ? 1'b1 : tx_eot ? 1'b0 : ref_sig ;
   property tx_sot_only_after_previous_tx_eot_received;
      @(posedge clk) disable iff(!rst_n)
       (ref_sig)  |=> ~(|tx_sot);
   endproperty

   assert_tx_sot_only_after_previous_tx_eot_received : assert property(tx_sot_only_after_previous_tx_eot_received)
   else
      $error("HTAX_TX_INF ERROR : tx_sot of p(t+1) without tx_eot for p(t)");



   // ------------------------------------------------------------- 
   // Valid packet transfer – rise of tx_outport_req followed by a tx_vc_gnt followed by tx_sot
	 // followed by tx_release_gnt followed by tx_eot. Consider the right timings between each event.
   // ------------------------------------------------------------- 

   property valid_packet_transfer;
      @(posedge clk) disable iff(!rst_n)
	((|tx_outport_req) |-> ##[1:$] (|tx_vc_gnt) ##1 (tx_sot) ##[0:$] tx_release_gnt ##1 tx_eot);      
   endproperty

   assert_valid_packet_transfer : assert property(valid_packet_transfer)
   else
      $error("HTAX_TX_INF ERROR : Not a Valid Packet Transfer");




endinterface : htax_tx_interface
