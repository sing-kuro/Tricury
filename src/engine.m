:- module engine.

:- interface.
:- use_module stype, usi, eval, nn.
:- import_module list, time, maybe, hash_table, bool.
:- import_module io.

:- func init = (enst::enst_out) is det.
:- pred usi(string::out, string::out, list({string,usi.option_type})::out, enst::enst_out) is det.
:- pred isready(enst::enst_di, enst::enst_out, io::di, io::uo) is det.
:- pred setoption(string::in, string::in, enst::enst_di, enst::enst_out) is det. 
:- pred usinewgame(enst::enst_di, enst::enst_out) is det.
:- pred position(stype.pos::in, stype.side::in, list(string)::in, enst::enst_di, enst::enst_out) is semidet.
:- pred go(usi.options::in, time.clock_t::in, enst::enst_di, enst::enst_out, io::di, io::uo) is det.
:- pred stop(enst::enst_di, enst::enst_out) is det.
:- pred ponderhit(time.clock_t::in, enst::enst_di, enst::enst_out) is det.
:- pred quit(enst::enst_di, enst::enst_out) is det.
:- pred gameover(stype.result::in, enst::enst_di, enst::enst_out) is det.

:- pred tick(time.clock_t::in, usi.info::out, maybe(stype.move)::out, maybe(stype.move)::out, enst::enst_di, enst::enst_out, io::di, io::uo, bool::out) is det. %fail on quit

% How do I hide these?
:- type enst
    --->   enst(
        is_running::bool,
        is_ready::bool,
        usi_ponder::bool,
        usi_hash::int,
        learn_from_game::bool,
        model_file::string,
        nn::nn.nn,
        maxdepth::int,
        maxtime::clock_t, % 0:no limit
        offset::clock_t, %how much earlier to play
        info_interval::clock_t,
        is_playing::bool,
        is_thinking::bool,
        is_pondering::bool,
        infinite::bool,
        solving_mate::bool,
        start_thinking::clock_t,
        time_limit::clock_t,
        byoyomi::clock_t,
        inc::clock_t,
        last_provided_info::clock_t,
        curr_state::engine.state,
        transposition_table::hash_table(stype.pos, eval.score),
        return_best::bool
    ).


:- type state
    --->    state(
        curr_pos::stype.pos,
        turn::stype.side,
        score::eval.score,
        next::list({engine.state, stype.move}),
        node::int,
        depth::int
    ).


:- inst enst for enst/0
    == bound(enst(ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, ground, hash_table, ground)).
:- mode enst_di == di(enst).
:- mode enst_out == out(enst).


:- implementation.
:- import_module int, require.
:- use_module gen, sfen.

init = State :-
    usi(_,_,_,State).

usi(
    "Tricury",
    "Kuro Amami",
    [
        {"USI_Ponder", usi.check},
        {"USI_Hash", usi.spin},
        {"learn_from_game", usi.check},
        {"model_file", usi.filename},
        {"max_depth", usi.spin},
        {"max_time(s)", usi.spin},
        {"offset(ms)", usi.spin},
        {"info_interval(s)", usi.spin}
    ],
    enst(
        yes,
        no,
        yes,
        1024,
        no,
        "test.txt",
        nn.make_empty,
        5,
        clocks_per_sec * 36,
        clocks_per_sec // 100,
        clocks_per_sec * 1,
        no,
        no,
        no,
        no,
        no,
        0,
        0,
        0,
        0,
        0,
        state(
            stype.init_pos,
            stype.b,
            eval.not_evaluated,
            [],
            0,
            0
        ),
        hash_table.init_default(generic_hash),
        no
    )
).

isready(Enst, (Enst ^ is_ready := yes) ^ nn := NN, !IO):-
    eval.init(Enst ^ model_file, NN, !IO).

setoption(Option,Value,In,Out) :-
    (
        if  Option = "model_file"   then
            Out = In ^ model_file := Value
        else
            In = Out
    ).

usinewgame(Enst, Enst ^ is_playing := yes).

position(Startpos, Startside, SfenMoves, In, Out):-
    apply_sfen_move_list(Startpos, Startside, SfenMoves, Pos),
    (
        if
            even(list.length(SfenMoves))
        then
            Currside = Startside
        else
            stype.invert(Currside, Startside)
    ),
    NewState = engine.state(Pos, Currside, eval.not_evaluated, [], 0, 0),
    Tmp0 = (In ^ curr_state := NewState),
    Out = (Tmp0 ^ curr_state ^ turn := Currside).

:- pred apply_sfen_move_list(stype.pos::in, stype.side::in, list(string)::in, stype.pos::out) is semidet.
apply_sfen_move_list(Startpos, Startside, [SfenMove | L], Pos):-
    sfen.move(SfenMove, Startside, Startpos, Move),
    gen.apply(Startpos, Move, Pos0),
    apply_sfen_move_list(Pos0, stype.invert(Startside), L, Pos).
apply_sfen_move_list(Pos, _, [], Pos).

go(Options, Now, In, Out, !IO):-
    %write_string("start go\n", !IO),
    (
        if
            (Options ^ usi.infinite = yes ; Options ^ usi.mate = -1)
        then
            Infinite = yes
        else
            Infinite = no
    ),
    (
        if
            Options ^ usi.mate \= 0
        then
            Mate = yes,
            Limit = Options ^ usi.mate * time.clocks_per_sec // 1000,
            Inc = 0
        else
            Mate = no,
            (
                if
                    In ^ curr_state ^ turn = stype.b
                then
                    Limit = Options ^ usi.btime * time.clocks_per_sec // 1000,
                    Inc = Options ^ usi.binc * time.clocks_per_sec // 1000
                else
                    Limit = Options ^ usi.wtime * time.clocks_per_sec // 1000,
                    Inc = Options ^ usi.winc * time.clocks_per_sec // 1000
            )
   ),
    Out =
        (((((((((In 
        ^ start_thinking := Now)
        ^ is_thinking := yes)
        ^ is_pondering := Options ^ usi.ponder)
        ^ infinite := Infinite)
        ^ solving_mate := Mate)
        ^ time_limit := Limit)
        ^ byoyomi := Options ^ usi.byoyomi * time.clocks_per_sec // 1000)
        ^ inc := Inc)
        ^ return_best := no).

stop(In, Out):-
    Out =
        ((
            In
            ^ is_pondering := no)
            ^ return_best := yes).

ponderhit(Now, In, Out):-
    Out = (In ^ is_pondering := no) ^ start_thinking := Now.

quit(In, Out):-
    Out = In ^ is_running := no.

gameover(Result, In, Out):-
    Out = In ^ is_playing := no.

tick(_,usi.info(no,no,no,no,no,no,no,no,no,no),no,no,Enst @ enst(no,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_,_),Enst,!IO,no).
tick(Now, Info, BestMove, PonderMove, In @ enst(yes,IsReady,USI_Ponder, USI_Hash,LearnFromGame,ModelFile,NN,MaxDepth,MaxTime,Offset,InfoInterval,IsPlaying,IsThinking,IsPondering,Infinite,SolvingMate,StartThinking,TimeLimit,Byoyomi,Inc,LastProvidedInfo,CurrState,TranspositionTable,ReturnBest), Out, !IO, yes):-
    (
        if  Now - LastProvidedInfo > InfoInterval, IsThinking = yes
        then
            Info = usi.info(
                yes(CurrState ^ depth),
                no,
                yes((Now - StartThinking) * 1000 // clocks_per_sec),
                yes(CurrState ^ node),
                no,
                yes(eval.to_int(CurrState ^ score, CurrState ^ turn)),
                no,
                no,
                no,
                no
            ),
            ProvidedInfo = Now
            %ProvidedInfo = LastProvidedInfo
        else
            Info = usi.info(no,no,no,no,no,no,no,no,no,no),
            ProvidedInfo = LastProvidedInfo
    ),
    (
        if
            IsThinking = yes
        then
            (
                if
                    ReturnBest = yes
                then
                    (
                        if
                            best(CurrState, BestNo),
                            det_index0(CurrState ^ next, BestNo, {BestState, BestMove0}),
                            SolvingMate = no
                        then
                            BestMove = yes(BestMove0),
                            (
                                if
                                    USI_Ponder = yes,
                                    best(BestState, PonderNo),
                                    BestMove0 \= stype.claim
                                then
                                    det_index0(BestState ^ next, PonderNo, {_, PonderMove0}),
                                    (
                                        if  PonderMove0 \= stype.claim  then
                                            PonderMove = yes(PonderMove0)
                                        else
                                            PonderMove = no
                                    )
                                else 
                                    PonderMove = no
                            )
                        else
                            BestMove = yes(stype.resign),
                            PonderMove = no
                    ),
                    Out = ((In ^ return_best := no) ^ is_thinking := no) ^ last_provided_info := ProvidedInfo
                else
                    BestMove = no,
                    PonderMove =no,
                    (
                        if
                            (
                                Now - StartThinking < TimeLimit+Byoyomi+Inc-Offset,
                                Now - StartThinking < MaxTime,
                                CurrState ^ depth < MaxDepth + 1
                            ;
                                Infinite = yes
                            ;
                                IsPondering = yes
                            ),
                            (
                                1 < length(CurrState ^ next)
                            ;
                                CurrState ^ depth < 1
                            )
                        then
                            think(NN, CurrState, TranspositionTable, NewState, NewTable, _, !IO),
                            Out = ((In
                                ^ curr_state := NewState)
                                ^ transposition_table := NewTable)
                                ^ last_provided_info := ProvidedInfo
                        else
                            Out = (In ^ return_best := yes)
                                ^ last_provided_info := ProvidedInfo
                    )
            )
        else 
            BestMove = no,
            PonderMove = no,
            Out = In
    ).

:- pred think(nn.nn::in, engine.state::in, hash_table(stype.pos,eval.score)::hash_table_di, engine.state::out, hash_table(stype.pos,eval.score)::hash_table_uo, bool::out, io::di, io::uo) is det.
think(NN, OldState, !.Table, NewState, !:Table, NewDepth, !IO):- 
    (
        if
            OldState ^ depth = 0
        then
            (
                if
                    hash_table.search(!.Table, OldState ^ curr_pos, Score0)
                then
                    Score = Score0
                else
                    eval.eval(NN, OldState ^ curr_pos, OldState ^ turn) = Score,
                    hash_table.set(OldState ^ curr_pos, Score, !.Table, !:Table)
            ),
            %write_string("call generate_all\n",!IO),
            gen.generate_all(OldState ^ curr_pos, OldState ^ turn, NextPos),
            %write_string("generate_all succ\n", !IO),
            to_state(NextPos, stype.invert(OldState ^ turn), Next),            
            NewState = ((((OldState 
                ^ depth := 1) 
                ^ node := 0) 
                ^ score := Score) 
                ^ next := Next),
            NewDepth = yes
        else
            %write_string("depth1 think\n", !IO),
            (
                if  index0(OldState ^ next, OldState ^ node, {OldChild, Move})   then
                    (
                        if  Move \= stype.claim then
                            %write_string("depth0 call\n", !IO),
                            %write(OldChild,!IO),
                            think(NN, OldChild, !.Table, TmpChild, !:Table, Inc, !IO),
                            det_replace_nth(OldState ^ next, OldState ^ node + 1, {TmpChild, Move}, TmpNext),
                            TmpCurr = OldState ^ next := TmpNext,
                            (
                                if  Inc = yes   then
                                    inc_node(TmpCurr, NewState, NewDepth)
                                else
                                    NewState = TmpCurr,
                                    NewDepth = no
                            )
                        else
                            Tmp = (OldState ^ score := eval.invert(eval.claim)),
                            inc_node(Tmp, NewState, NewDepth)
                    )
               else
                    NewState = OldState,
                    NewDepth = yes
            )
    ).

:- pred to_state(list({stype.pos, stype.move})::in, stype.side::in, list({engine.state, stype.move})::out) is det.
to_state([{Pos, Move} | L], Turn, [{State, Move} | M]):-
    to_state(L, Turn, M),
    State = state(
        Pos, Turn, eval.not_evaluated, [], 0, 0
    ).
to_state([], _, []).
    

:- pred inc_node(engine.state::in, engine.state::out, bool::out) is det.
inc_node(OldState, NewState, NewDepth):- 
    Len = length(OldState ^ next),
    (OldState ^ depth = 0 -> error("inc was called when depth is 0") ; true),
    (
        if
            OldState ^ node + 1 < Len
        then
            NewState = OldState ^ node := (OldState ^ node + 1),
            NewDepth = no
        else
            best_score(OldState, Score),
            (
                if  Score \= eval.not_evaluated then
                    NewState = ((OldState ^ node := 0) ^ depth := (OldState ^ depth + 1)) ^ score := eval.invert(Score) 
                else 
                    NewState = ((OldState ^ node := 0) ^ depth := (OldState ^ depth + 1))
            ),
            NewDepth = yes
    ).

:- pred best(engine.state::in, int::out) is semidet. %fail on resign
best(State, No):-
    \+ is_empty(State ^ next),
    max_pos(State ^ next, No).

:- pred best_score(engine.state::in, eval.score::out) is det.
best_score(State, Score):-
    max_score(State ^ next, Score).

:- pred max_pos(list({engine.state, stype.move})::in, int::out) is semidet.
max_pos(L, Index):-
    max_score(L,Score),
    find_score(L, Score, Index).


:- pred find_score(list({engine.state, stype.move})::in, eval.score::in, int::out) is semidet.
find_score([{State, _} | L], Score, Index):-
    (
        if
            State ^ score = Score
        then 
            Index = 0
        else 
            find_score(L, Score, Idx),
            Index = Idx + 1
    ).

:- pred max_score(list({engine.state, stype.move})::in, eval.score::out) is det.
max_score([{S,_}|L], Out):-
    max_score(L, Score),
    (
        if
            compare(Comp, Score, S ^ score),
            Comp = (<)
        then
            Out = S ^ score
        else 
            Out = Score
    ).
max_score([], eval.score(min_int)).
