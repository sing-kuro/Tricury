:- module eval.
:- interface.
:- import_module io.
:- use_module stype, nn.

:- type score
    ---> resign
    ;   score(int)
    ;   claim
    ;   not_evaluated.

:- pred win(stype.pos::in, stype.side::in) is semidet.
:- func eval(nn.nn, stype.pos, stype.side) = score. % return score from side's prespective
:- func to_int(score, stype.side) = int.
:- func invert(score) = score.

:- pred init(string::in, nn.nn::out, io::di, io::uo) is det.

:- implementation.
:- import_module int, gen, float, require, maybe, list, bool.
win(Pos,Side) :- gen.claim(Pos,Side).

eval(NN, Pos, Side) = Score:-
    (
        if  win(Pos, Side)  then
            Score = eval.claim
        else
            eval.trichotomize(NN, Pos, Side, Res),
            Score = score(Res)
            %Score = score(stype.side_int(Side) * 10)
    ).

:- pred trichotomize(nn.nn::in, stype.pos::in, stype.side::in, int::out) is det.
trichotomize(NN, Pos, Side, Result):- 
    pos2vec(Pos, Side, In),
    nn.unsafe_forward(NN, In, Out),
    nn.unsafe_at(Out,0,Win),
    nn.unsafe_at(Out,1,Draw),
    nn.unsafe_at(Out,2,Lose),
    (
        if  Draw < Win, Lose < Win  then
            Result = float.round_to_int(Win*100.0)
        else if Win < Lose, Draw < Lose then
            Result = float.round_to_int(-Lose*100.0)
        else
            Result = 0
    ).

init(File, NN, !IO) :-  
    nn.load(File, Res, !IO),
    (Res = ok(NN0) -> NN = NN0 ; error("failed to load model file")).

:- pred pos2vec(stype.pos::in, stype.side::in, nn.vect(float)::out) is det.
pos2vec(Pos, Side, nn.sparse(28*81+14,0.0,L)):-
    pos2list(Pos, Side, -48, [], L).

:- pred pos2list(stype.pos::in, stype.side::in, int::in, list({int,float})::in, list({int,float})::out) is det.
pos2list(Pos, Side, Index, Acc, Return):-
    (
        if  Index < 49 then
            (
                if  stype.get_square(Pos, Index, PieceSide, Piece, Promoted)    then
                    Hot = (Index * stype.side_int(Side) + 40) * 28 + piece_int(Piece) + opponents(Side,PieceSide) + promoted(Promoted),
                    list.append(Acc, [{Hot,1.0}], Acc0)
                else
                    Acc0 = Acc
            ),
            pos2list(Pos, Side, Index+1, Acc0, Return)
        else if Index = 49  then
            get_hand(Pos, Side, R,B,G,S,N,L,P),
            Base = 81 * 28,
            list.append(Acc, [{Base,float(R)},{Base+1,float(B)},{Base+2,float(G)},{Base+3,float(S)},{Base+4,float(N)},{Base+5,float(L)},{Base+6,float(P)}], Acc0),
            pos2list(Pos, Side, Index+1, Acc0, Return)
        else if Index = 50  then
            get_hand(Pos, stype.invert(Side), R,B,G,S,N,L,P),
            Base = 81 * 28 + 7,
            list.append(Acc, [{Base,float(R)},{Base+1,float(B)},{Base+2,float(G)},{Base+3,float(S)},{Base+4,float(N)},{Base+5,float(L)},{Base+6,float(P)}], Return)
        else    error("pos2list wrong index")
    ).

:- func piece_int(stype.piece) = int.
piece_int(stype.k) = 0.
piece_int(stype.r) = 3.
piece_int(stype.b) = 2.
piece_int(stype.g) = 1.
piece_int(stype.s) = 4.
piece_int(stype.n) = 5.
piece_int(stype.l) = 6.
piece_int(stype.p) = 7.
:- func promoted(bool) = int.
promoted(no) = 0.
promoted(yes) = 6.
:- func opponents(stype.side, stype.side) = int.
opponents(Side,Piece)=N:-
    (
        if  Side = Piece    then
            N = 0
        else
            N = 14
    ).

:- pred get_hand(stype.pos::in, stype.side::in, int::out,int::out,int::out,int::out,int::out,int::out,int::out) is det.
get_hand(Pos, Side, R,B,G,S,N,L,P):-
    stype.hand(Hand, Side),
    stype.extract(Pos,stype.r,RL),
    stype.extract(Pos,stype.b,BL),
    stype.extract(Pos,stype.g,GL),
    stype.extract(Pos,stype.s,SL),
    stype.extract(Pos,stype.n,NL),
    stype.extract(Pos,stype.l,LL),
    stype.extract(Pos,stype.p,PL),
    count(stype.piece_state(Hand,Side,no),RL,R),
    count(stype.piece_state(Hand,Side,no),BL,B),
    count(stype.piece_state(Hand,Side,no),GL,G),
    count(stype.piece_state(Hand,Side,no),SL,S),
    count(stype.piece_state(Hand,Side,no),NL,N),
    count(stype.piece_state(Hand,Side,no),LL,L),
    count(stype.piece_state(Hand,Side,no),PL,P).

:- pred count(T::in, list(T)::in, int::out) is det.
count(Elem, [A|L], Num):-
    count(Elem, L, Num0),
    (
        if  Elem = A    then
            Num = Num0 + 1
        else
            Num = Num0
    ).
count(_,[],0).

to_int(score(S), Side) = S * stype.side_int(Side).
to_int(resign, stype.b) = -30000.
to_int(resign, stype.w) = 30000.
to_int(claim, stype.b) = 30000.
to_int(claim, stype.w) = -3000.
to_int(not_evaluated, _) = -1.

invert(resign) = score(max_int).
invert(claim) = resign.
invert(score(N)) = score(-N).
invert(not_evaluated) = not_evaluated.