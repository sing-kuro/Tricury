:- module sfen.
:- interface.
:- use_module stype.
:- pred move(string::in, stype.side::in, stype.pos::in, stype.move::out) is semidet.
:- pred move(string::out, stype.move::in) is semidet.
:- func move(stype.move::in) = (string::out) is det.
:- pred pos(string::in, stype.pos::out) is semidet.
:- func pos(string) = stype.pos is semidet.
:- implementation.
:- import_module string,char,list,bool,int,io,require.

move(Sfen, stype.move(Src,Dst,Piece,Promote)):- 
    Tmp0 = [],
    ( if 
        stype.hand(Src,_)
    then
        append([from_piece(Piece),'*'],Tmp0,Tmp1)
    else
        append([col(Src),row(Src)],Tmp0,Tmp1)
    ),
    append(Tmp1,[col(Dst),row(Dst)],Tmp2),
    ( if
        Promote = bool.yes
    then
        append(Tmp2,['+'],Slist)
    else
        Slist = Tmp2
    ),
    string.from_char_list(Slist, Sfen).

move("resign", stype.resign).
move("win", stype.claim).
move(Move) = Sfen :-
    (move(Sfen0, Move) -> Sfen0 = Sfen ; error("invalid move")).
 
move(Sfen, Side, Pos, stype.move(Src,Dst,Piece,Promote)):-
    string.to_char_list(Sfen, Slist),
    (
        if 
            member_index0('*',Slist,1)
        then
            stype.hand(Src,Side),
            det_index0(Slist,0,P),
            to_piece(P,Piece),
            Promote = bool.no
        else
            det_index0(Slist,0,SCol),
            det_index0(Slist,1,SRow),
            square(SCol,SRow,Src),
            promise_equivalent_solutions([Piece],
            stype.occupied(Pos,Src,Piece)),
            (
                if 
                    length(Slist,5)
                then
                    Promote = bool.yes
                else
                    Promote = bool.no
            )
    ),
    det_index0(Slist,2,DCol),
    det_index0(Slist,3,DRow),
    square(DCol,DRow,Dst).

   
pos("startpos", stype.init_pos).
pos(Sfen) = Pos :-
    pos(Sfen,Pos).

:- pred from_piece(stype.piece, char).
:- mode from_piece(in, out) is det.
from_piece(Piece, Char):-
    det_index0(to_char_list(string.to_upper(string.string(Piece))),0) = Char.
:- pred to_piece(char::in, stype.piece::out) is semidet.
to_piece(Char, Piece):-
    Term = from_char_list([to_lower(Char)]) ++ ".",
    io.read_from_string("input to to_piece",Term,2,ok(Piece),io.posn(0,0,0),_).
:- func from_piece(stype.piece) = char.
from_piece(Piece) = Char :-
    from_piece(Piece,Char).

:- pred col(int::in, char::out) is semidet.
col(Field, Col):-
    Ans = (5 - (Field mod 11)) mod 11,
    0 < Ans, Ans < 10,
    from_int(Ans + to_int('0'), Col).
:- func col(int) = char is semidet.
col(Field) = Char :- col(Field,Char).

:- pred row(int::in, char::out) is semidet.
row(Field, Row):-
    Ans = (Field + 5) div 11 + 4,
    from_int(Ans + to_int('a'), Row).
:- func row(int) = char is semidet.
row(Field) = Char :- row(Field,Char).

:- pred square(char::in, char::in, int::out) is semidet.
square(CCol, CRow, Field):-
    ICol = to_int(CCol) - to_int('0'),
    IRow = to_int(CRow) - to_int('a') - 4,
    0 < ICol, ICol < 10,
    -5 < IRow, IRow < 5,
    Field = IRow * 11 + 5 - ICol.