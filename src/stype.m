:- module stype.
:- interface.
:- import_module list, bool.
:- type side
	--->	b
	;	w.
:- type result
	--->	win
	;	lose
	;	draw.
:- type piece
	--->	k
	;	r
	;	b
	;	g
	;	s
	;	n
	;	l
	;	p.
:- type piece_state
	--->	piece_state(square::int, side::side, promote::bool).
:- type pos
	--->	pos(
		k::list(piece_state),
		r::list(piece_state),
		b::list(piece_state),
		g::list(piece_state),
		s::list(piece_state),
		n::list(piece_state),
		l::list(piece_state),
		p::list(piece_state)).
:- type move
	--->	move( src::int, dst::int, name::piece, pro::bool)
	;	resign
	;	claim.

% need to define the hash predicate for pos.

:- pred hand(int, side).
:- mode hand(in, in) is semidet.
:- mode hand(in, out) is semidet.
:- mode hand(out, in) is det.
:- mode hand(out, out) is multi.

:- pred side_int(side,int).
:- mode side_int(in, in) is semidet.
:- mode side_int(in, out) is det.
:- mode side_int(out, in) is semidet.
:- mode side_int(out, out) is multi.
:- func side_int(side) = int.

:- pred on_board(int).
:- mode on_board(in) is semidet.
:- mode on_board(out) is nondet. %intended to be multi

:- pred territory(int, side).
:- mode territory(in, in) is semidet.
:- mode territory(in, out) is cc_nondet.
:- mode territory(out, in) is nondet. %intended to be multi

:- pred last_rank(stype.side, int).
:- mode last_rank(in, in) is semidet.
:- mode last_rank(out, in) is cc_nondet.
:- mode last_rank(in, out) is multi.

:- pred last2rank(stype.side, int).
:- mode last2rank(in, in) is semidet.
:- mode last2rank(out, in) is cc_nondet.
:- mode last2rank(in, out) is multi.

:- pred occupied(pos,int,piece).
:- mode occupied(in, in, in) is semidet.
:- mode occupied(in, in, out) is cc_nondet.
:- mode occupied(in, out, out) is nondet.

:- pred occupied_side(pos,int,side).
:- mode occupied_side(in, in, in) is semidet.

:- pred exist(pos,piece,side,int,bool).
:- mode exist(in, in, in, out, out) is nondet.
:- mode exist(in, in, in, in, in) is semidet.
:- mode exist(in, out, in, out, out) is nondet.

:- pred init_pos(pos::out) is det.
:- func init_pos = pos.

:- pred invert(side, side).
:- mode invert(in, in) is semidet.
:- mode invert(in, out) is det.
:- mode invert(out,in) is det.
:- mode invert(out, out) is multi.
:- func invert(side) = side.

:- pred extract(pos, piece, list(piece_state)).
:- mode extract(in,in,out) is det.
:- mode extract(in,out,in) is cc_nondet.
:- mode extract(in,out,out) is multi.

:- pred combine(pos::in, list(piece_state)::in, piece::in, pos::out) is det.

:- pred get_square(pos::in, int::in, side::out, piece::out, bool::out) is semidet.

:- pred hand_piece(pos::in, side::in, piece::out) is nondet.

:- implementation.
:- import_module string, int, require.

hand(100,b).
hand(-100,w).
side_int(b,1).
side_int(w,-1).
side_int(Side) = Int :- side_int(Side,Int).
on_board(Field):-
	between(-48, 48, Field),
	Field mod 11 = Mod,
	Mod \= 6,
	Mod \= 5.

:- pred between(int, int, int).
:- mode between(in, in, in) is semidet.
:- mode between(in, in, out) is multi.
between(Min, Max, Int):-
	(
		if  Min > Max	then
			error("min greater than max")
		else if	Min = Max	then
			Min = Int
		else
			(
				Int = Min + 1
			;
				between(Min + 1, Max, Int)
			)
	).

territory(Field,Side):-
	side_int(Side,N),
	Field * N > 17,
	on_board(Field).

last_rank(b, Field) :- between(-48, -40, Field).
last_rank(w, Field) :- between(40, 48, Field).

last2rank(b, Field) :- between(-48, -29, Field).
last2rank(w, Field) :- between(29, 48, Field).

invert(b,w).
invert(w,b).
invert(Side) = Oppo :-
	invert(Side, Oppo).

init_pos(pos([stype.piece_state(44,stype.b,no),stype.piece_state(-44,stype.w,no)],[stype.piece_state(36,stype.b,no),stype.piece_state(-36,stype.w,no)],[stype.piece_state(30,stype.b,no),stype.piece_state(-30,stype.w,no)],[stype.piece_state(43,stype.b,no),stype.piece_state(45,stype.b,no),stype.piece_state(-43,stype.w,no),stype.piece_state(-45,stype.w,no)],[stype.piece_state(42,stype.b,no),stype.piece_state(46,stype.b,no),stype.piece_state(-42,stype.w,no),stype.piece_state(-46,stype.w,no)],[stype.piece_state(41,stype.b,no),stype.piece_state(47,stype.b,no),stype.piece_state(-41,stype.w,no),stype.piece_state(-47,stype.w,no)],[stype.piece_state(40,stype.b,no),stype.piece_state(48,stype.b,no),stype.piece_state(-40,stype.w,no),stype.piece_state(-48,stype.w,no)],[stype.piece_state(18,stype.b,no),stype.piece_state(19,stype.b,no),stype.piece_state(20,stype.b,no),stype.piece_state(21,stype.b,no),stype.piece_state(22,stype.b,no),stype.piece_state(23,stype.b,no),stype.piece_state(24,stype.b,no),stype.piece_state(25,stype.b,no),stype.piece_state(26,stype.b,no),stype.piece_state(-18,stype.w,no),stype.piece_state(-19,stype.w,no),stype.piece_state(-20,stype.w,no),stype.piece_state(-21,stype.w,no),stype.piece_state(-22,stype.w,no),stype.piece_state(-23,stype.w,no),stype.piece_state(-24,stype.w,no),stype.piece_state(-25,stype.w,no),stype.piece_state(-26,stype.w,no)])).
init_pos = Pos :-
	init_pos(Pos).

occupied(pos(X,_,_,_,_,_,_,_), Field, k):-
	member(piece_state(Field,_,_),X).
occupied(pos(_,X,_,_,_,_,_,_), Field, r):-
	member(piece_state(Field,_,_),X).
occupied(pos(_,_,X,_,_,_,_,_), Field, b):-
	member(piece_state(Field,_,_),X).
occupied(pos(_,_,_,X,_,_,_,_), Field, g):-
	member(piece_state(Field,_,_),X).
occupied(pos(_,_,_,_,X,_,_,_), Field, s):-
	member(piece_state(Field,_,_),X).
occupied(pos(_,_,_,_,_,X,_,_), Field, n):-
	member(piece_state(Field,_,_),X).
occupied(pos(_,_,_,_,_,_,X,_), Field, l):-
	member(piece_state(Field,_,_),X).
occupied(pos(_,_,_,_,_,_,_,X), Field, p):-
	member(piece_state(Field,_,_),X).

occupied_side(Pos, Field, Side):-
	extract(Pos, _, L),
	member(piece_state(Field,Side,_), L).

exist(Pos, Piece, Side, Field, Promoted):- 
	extract(Pos,Piece,L),
	member(piece_state(Field, Side, Promoted), L).

extract(Pos, k, Pos ^ k).
extract(Pos, r, Pos ^ r).
extract(Pos, b, Pos ^ b).
extract(Pos, g, Pos ^ g).
extract(Pos, s, Pos ^ s).
extract(Pos, n, Pos ^ n).
extract(Pos, l, Pos ^ l).
extract(Pos, p, Pos ^ p).

combine(Pos, L, k, New):- New = Pos ^ k := L.
combine(Pos, L, r, New):- New = Pos ^ r := L.
combine(Pos, L, b, New):- New = Pos ^ b := L.
combine(Pos, L, g, New):- New = Pos ^ g := L.
combine(Pos, L, s, New):- New = Pos ^ s := L.
combine(Pos, L, n, New):- New = Pos ^ n := L.
combine(Pos, L, l, New):- New = Pos ^ l := L.
combine(Pos, L, p, New):- New = Pos ^ p := L.

get_square(Pos, Field, Side, Piece, Promoted):-
	promise_equivalent_solutions(
		[Side,Piece,Promoted],
		(
			extract(Pos, Piece, L),
			member(piece_state(Field,Side,Promoted),L)
		)
	).

hand_piece(Pos, Side, Piece):-
	hand(Field, Side),
	extract(Pos, Piece, L),
	promise_equivalent_solutions(
		[],
		member(piece_state(Field, Side, no), L)
	).