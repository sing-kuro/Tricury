:- module usi.

:- interface.
:- use_module stype.
:- import_module bool, list, maybe.


:- type options
	---> 	options(
		ponder::bool,
		btime::int, 
		wtime::int, 
		byoyomi::int, 
		binc::int, 
		winc::int, 
		infinite::bool, 
		mate::int/*0:not mate,-1:infinite,other::time*/
		).

:- type info
	--->	info(
		depth::maybe(int), 
		seldepth::maybe(int), 
		time::maybe(int), 
		nodes::maybe(int), 
		pv::maybe(list(stype.move)), 
		cp::maybe(int), 
		mate::maybe(int), 
		currmove::maybe(stype.move), 
		hashfull::maybe(int), 
		nps::maybe(int)
		).
:- func info_init = info.

:- type option_type
	--->	check
	;	spin
	;	combo
	;	button
	;	string
	;	filename.

:- implementation.
info_init = info(no,no,no,no,no,no,no,no,no,no).