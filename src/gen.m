:- module gen.
:- interface.
:- use_module stype.
:- import_module list.
:- pred generate(stype.pos::in, stype.side::in, {stype.pos, stype.move}::out) is nondet. % generate claim too
:- pred apply(stype.pos::in, stype.move::in, stype.pos::out) is semidet.
:- pred generate_all(stype.pos::in, stype.side::in, list({stype.pos, stype.move})::out) is det.
:- pred claim(stype.pos::in, stype.side::in) is semidet.
:- implementation.
:- import_module solutions, bool, int, io, string.


generate_all(Pos, Side, List):-
    solutions(generate(Pos, Side), List).

%claim
generate(Pos, Side, {Pos,stype.claim}):-
    claim(Pos, Side).
%move
generate(Pos, Side, {Newpos, Move @ stype.move(Src, Dst, Piece, Pro)}):-
    trace [compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("Try generate non-claim.\n", !IO)
    ),
    valid_move(Pos, Side, Move),
    trace [compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("consider: ", !IO),
        io.write(Move, !IO),
        io.write_string(" in pos\n", !IO),
        io.write(Pos, !IO),
        nl(!IO)
    ),
    gen.apply(Pos, Move, Newpos),
    trace [compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("newpos: ", !IO),
        io.write(Newpos, !IO),
        nl(!IO)
    ),
    (
        if  Pro = no    then
            \+ nowhere2go(Newpos, Dst, Side, Piece),
            (
                if  stype.hand(Src, Side), Piece = stype.p then
                    stype.invert(Side, Oppo),
                    \+ double_pawn(Newpos, Side),
                    \+ checkmate(Oppo, Newpos)
                else
                    true
            )
        else
            true
    ),
    trace [compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("Call in_check(" ++ string(Side) ++ ", " ++ string(Newpos), !IO),
        io.nl(!IO)
    ),
    \+ in_check(Side, Newpos).

claim(Pos, stype.b) :- claim_points(Pos, stype.b, 28).
claim(Pos, stype.w) :- claim_points(Pos, stype.w, 27).

:- pred claim_points(stype.pos::in, stype.side::in, int::in) is semidet.
claim_points(Pos, Side, Points):- 
    gyoku_in(Pos, Side),
    \+ in_check(Side, Pos),
    points(Pos, Side, P),
    Points =< P,
    in_zone(Pos, Side, N),
    10 =< N.

:- pred gyoku_in(stype.pos::in, stype.side::in) is semidet.
gyoku_in(Pos, Side):- 
    stype.exist(Pos, stype.k, Side, Field, no),
    stype.invert(Side, Oppo),
    stype.territory(Field, Oppo).

:- pred points(stype.pos::in, stype.side::in, int::out) is det.
points(Pos, Side, Points):- 
    count_major(Pos, Side, Major),
    count_minor(Pos, Side, Minor),
    Points = Major * 5 + Minor.

:- pred count_major(stype.pos::in, stype.side::in, int::out) is det.
count_major(Pos, Side, Num):-
    count(Pos, Side, stype.r, R),
    count(Pos, Side, stype.b, B),
    Num = R + B.

:- pred count_minor(stype.pos::in, stype.side::in, int::out) is det.
count_minor(Pos, Side, Num):-
    count(Pos, Side, stype.g, G),
    count(Pos, Side, stype.s, S),
    count(Pos, Side, stype.n, N),
    count(Pos, Side, stype.l, L),
    count(Pos, Side, stype.p, P),
    Num = G+S+N+L+P.

:- pred count(stype.pos::in, stype.side::in, stype.piece::in, int::out) is det.
count(Pos, Side, Piece, Num):-
    stype.extract(Pos, Piece, L),
    count_rec(Side, L, Num).

:- pred count_rec(stype.side::in, list(stype.piece_state)::in, int::out) is det.
count_rec(_, [], 0).
count_rec(Side, [stype.piece_state(Field,Side2,_)|L],N):-
    count_rec(Side,L,M),
    stype.invert(Side,Oppo),
    (
        if  Side = Side2,(stype.hand(Field,Side);stype.territory(Field,Oppo))    then
            N = M+1
        else
            N = M
    ).

:- pred in_zone(stype.pos::in, stype.side::in, int::out) is det.
in_zone(Pos, Side, Num):- 
    in_count(Pos, Side, stype.r, R),
    in_count(Pos, Side, stype.b, B),
    in_count(Pos, Side, stype.g, G),
    in_count(Pos, Side, stype.s, S),
    in_count(Pos, Side, stype.n, N),
    in_count(Pos, Side, stype.l, L),
    in_count(Pos, Side, stype.p, P),
    Num = R+B+G+S+N+L+P.

:- pred in_count(stype.pos::in, stype.side::in, stype.piece::in, int::out) is det.
in_count(Pos, Side, Piece, N):-
    stype.extract(Pos, Piece, L),
    in_count_rec(Side, L, N).

:- pred in_count_rec(stype.side::in, list(stype.piece_state)::in, int::out) is det.
in_count_rec(_, [], 0).
in_count_rec(Side, [stype.piece_state(Field,Side2,_)|L],N):-
    stype.invert(Side, Oppo),
    in_count_rec(Side, L, M),
    (
        if  stype.territory(Field, Oppo), Side = Side2    then
            N = M + 1
        else 
            N = M
    ).

        
:- pred double_pawn(stype.pos::in, stype.side::in) is semidet.
double_pawn(Pos, Side):-
    stype.exist(Pos,stype.p,Side,F1,no),
    stype.exist(Pos,stype.p,Side,F2,no),
    F1 \= F2,
    F1 mod 11 = F2 mod 11,
    trace [compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("double_pawn succ.\n", !IO)
    ).

:- pred nowhere2go(stype.pos, int, stype.side, stype.piece).
:- mode nowhere2go(in, in, in, in) is semidet.
nowhere2go(Pos, Field, Side, Piece):-
    (
        (
            Piece = stype.p
        ;
            Piece = stype.l
        ),
        stype.last_rank(Side, Field)
    ;
        Piece = stype.n,
        stype.last2rank(Side, Field)
    ),
    stype.exist(Pos, Piece, Side, Field, no),
    trace [compile_time(flag("do_logging")),io(!IO)] (
        io.write_string("nowhere2go succ.\n", !IO)
    ).

apply(Pos, stype.move(Src,Dst,Piece,Promote), Newpos):-
    trace [compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("try apply " ++ string(stype.move(Src,Dst,Piece,Promote)) ++ " to\n" ++ string(Pos), !IO),
        io.nl(!IO) 
    ),
    (
        if  stype.hand(Src,Side)    then
            \+ stype.occupied(Pos, Dst, _),
            stype.extract(Pos, Piece, L1),
            remove(stype.piece_state(Src, Side, no), L1, L2),
            append([stype.piece_state(Dst, Side, no)], L2, L3),
            stype.combine(Pos, L3, Piece, Newpos)
        else
            stype.get_square(Pos,Src,Side,Piece,Promoted),
            stype.invert(Side,Oppo),
            or(Promoted,Promote,P),
            (
                if
                    stype.get_square(Pos,Dst,Oppo,TakePiece,TakePromoted)
                then
                    stype.hand(Hand,Side),
                    (
                        if  Piece = TakePiece   then
                            stype.extract(Pos,Piece,L1),
                            remove(stype.piece_state(Src,Side,Promoted),L1,L2),
                            remove(stype.piece_state(Dst,Oppo,TakePromoted),L2,L3),
                            append([stype.piece_state(Dst,Side,P),stype.piece_state(Hand,Side,no)],L3, L4),
                            stype.combine(Pos,L4,Piece,Newpos)
                        else
                            stype.extract(Pos,Piece,L1),
                            remove(stype.piece_state(Src,Side,Promoted),L1,L2),
                            append([stype.piece_state(Dst,Side,P)],L2,L3),
                            stype.combine(Pos,L3,Piece,Pos1),
                            stype.extract(Pos1,TakePiece,L4),
                            remove(stype.piece_state(Dst,Oppo,TakePromoted),L4,L5),
                            append([stype.piece_state(Hand,Side,no)],L5,L6),
                            stype.combine(Pos1,L6,TakePiece,Newpos)
                    )
                else
                    stype.extract(Pos, Piece, L1),
                    remove(stype.piece_state(Src,Side,Promoted),L1,L2),
                    append([stype.piece_state(Dst,Side,P)],L2,L3),
                    stype.combine(Pos,L3,Piece,Newpos)
        
            )
   ).

:- pred valid_move(stype.pos, stype.side, stype.move).
:- mode valid_move(in, in, in) is semidet.
:- mode valid_move(in, in, out) is nondet.
valid_move(Pos, Side, stype.move(Src, Dst, Piece, Promote)):-
    (
        stype.hand(Src,Side),
        drop(Pos, Side, Dst, Piece),
        Promote = no
    ;
        stype.exist(Pos, Piece, Side, Src, Promoted),
        stype.invert(Side, Oppo),
        (
            Promoted = no,
            (stype.territory(Dst, Oppo) ; stype.territory(Src, Oppo)),
            promotable(Piece),
            Promote = yes
        ;
            Promote = no
        ),
        poss_move(Piece, Promoted, Dir, Multi),
        stype.side_int(Side,N),
        (
            if  Multi = yes then
                multiple_steps(Pos, Src, Dst, Dir * N, Side)
            else
                single_step(Pos, Src, Dst, Dir * N, Side)
        )
    ),
    trace[compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("valid_move succ\n", !IO)
    ).

:- pred drop(stype.pos, stype.side, int, stype.piece).
:- mode drop(in, in, in, in) is semidet.
:- mode drop(in, in, out, out) is nondet.
drop(Pos, Side, Dst, Piece):-
    stype.hand_piece(Pos, Side, Piece),
    stype.on_board(Dst),
    \+ stype.occupied(Pos, Dst, _),
    trace[compile_time(flag("do_logging")), io(!IO)] (
        io.write_string("drop succ\n", !IO)
    ).

:- pred in_check(stype.side::in, stype.pos::in) is semidet.
in_check(Side, Pos):-
    stype.invert(Side, Oppo),
    stype.exist(Pos, stype.k, Side, King, no),
    valid_move(Pos, Oppo, stype.move(Src, King, Piece, _)),
    stype.exist(Pos, Piece, Oppo, Src, _),
    trace [compile_time(flag("do_logging")), io(!IO)] (
        write_string("in_check succ.\n", !IO),
        write(Piece, !IO),
        write_string(" can capture the king from field ", !IO),
        write_int(Src, !IO),
        nl(!IO),
        write(Pos, !IO),
        nl(!IO)
    ).

:- pred checkmate(stype.side::in, stype.pos::in) is semidet.
checkmate(Side, Pos):-
    in_check(Side, Pos),
    \+ generate(Pos, Side, _).

:- pred single_step(stype.pos, int, int, int, stype.side).
:- mode single_step(in, in, in, in, in) is semidet.
:- mode single_step(in, in, out, in, in) is semidet.
single_step(Pos, Src, Dst, Dir, Side):-
    Dst = Src + Dir,
    stype.on_board(Dst),
    (
        \+ stype.occupied(Pos, Dst, _)
    ;
        stype.invert(Side, Oppo),
        stype.occupied_side(Pos, Dst, Oppo)
    ).

:- pred multiple_steps(stype.pos, int, int, int, stype.side).
:- mode multiple_steps(in, in, in, in, in) is semidet.
:- mode multiple_steps(in, in, out, in, in) is nondet.
multiple_steps(Pos, Src, Dst, Dir, Side):-
    single_step(Pos, Src, Next, Dir, Side),
    (
        Next = Dst
    ;
        \+ stype.occupied(Pos, Next, _),
        multiple_steps(Pos, Next, Dst, Dir, Side)
    ).


:- pred remove(stype.piece_state::in, list(stype.piece_state)::in, list(stype.piece_state)::out) is semidet.
remove(X, [A|L], M):-
    (
        if  X = A   then
            L = M
        else
            M = [A|B],
            remove(X, L, B)
    ).

:- pred poss_move(stype.piece, bool, int, bool).
:- mode poss_move(in, in, out, out) is nondet.
:- mode poss_move(in, in, out, in) is nondet.

poss_move(stype.k, no, X, no) :- poss_move(stype.r, yes, X, _).

poss_move(stype.r, no, 11, yes).
poss_move(stype.r, no, -11, yes).
poss_move(stype.r, no, 1, yes).
poss_move(stype.r, no, -1, yes).
poss_move(stype.r, yes, X, yes) :- poss_move(stype.r, no, X, yes).
poss_move(stype.r, yes, X, no) :- poss_move(stype.b, no, X, yes).

poss_move(stype.b, no, 10, yes).
poss_move(stype.b, no, 12, yes).
poss_move(stype.b, no, -10, yes).
poss_move(stype.b, no, -12, yes).
poss_move(stype.b, yes, X, yes) :- poss_move(stype.b, no, X, yes).
poss_move(stype.b, yes, X, no) :- poss_move(stype.r, no, X, yes).

poss_move(stype.g, no, -10, no).
poss_move(stype.g, no, -12, no).
poss_move(stype.g, no, X, no) :- poss_move(stype.r, no, X, yes).

poss_move(stype.s, no, -11, no).
poss_move(stype.s, no, X, no) :- poss_move(stype.b, no, X, yes).
poss_move(stype.s, yes, X, no) :- poss_move(stype.g, no, X, no).

poss_move(stype.n, no, -21, no).
poss_move(stype.n, no, -23, no).
poss_move(stype.n, yes, X, no) :- poss_move(stype.g, no, X, no).

poss_move(stype.l, no, -11, yes).
poss_move(stype.l, yes, X, no) :- poss_move(stype.g, no, X, no).

poss_move(stype.p, no, -11, no).
poss_move(stype.p, yes, X, no) :- poss_move(stype.g, no, X, no).

:- pred promotable(stype.piece::in) is semidet.
promotable(stype.r).
promotable(stype.b).
promotable(stype.s).
promotable(stype.n).
promotable(stype.l).
promotable(stype.p).
