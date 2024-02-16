:- module inter.
:- interface.
:- import_module io.
:- pred main(io::di, io::uo) is cc_multi.
:- implementation.
:- import_module int, string, char, list, thread, thread.semaphore, time, maybe, bool, require.
:- use_module stype,engine,usi,sfen.


:- mutable(cmd, string, "", ground, [untrailed, attach_to_io_state]).
:- mutable(enst, engine.enst, engine.init, engine.enst, [untrailed, attach_to_io_state]).
:- mutable(running, bool, yes, ground, [untrailed, attach_to_io_state]).

main(!IO):-
    init(1, CmdSem, !IO),
    init(1, RunSem, !IO),
    spawn_native(input(CmdSem, RunSem), ResInput, !IO),
    spawn_native(rec(CmdSem, RunSem), ResRec, !IO).
    %(ResInput = error(InputErrorStr) -> write_string(InputErrorStr, !IO) ; write_string("input succ\n", !IO)),
    %(ResRec = error(RecErrorStr) -> write_string(RecErrorStr, !IO) ; write_string("rec succ\n", !IO)).

:- pred rec(semaphore::in, semaphore::in, thread::in, io::di, io::uo) is cc_multi.
rec(CmdSem, RunSem, Thread, !IO):-
    wait(CmdSem, !IO),
    get_cmd(Cmd, !IO),
    set_cmd("", !IO),
    signal(CmdSem, !IO),
    %write_string("call call_engine/4\n", !IO),
    call_engine(Cmd, Next, !IO),
    %write_string("call_engine/4 ended\n", !IO),
    (
        if
            Next = yes
        then 
            rec(CmdSem, RunSem, Thread, !IO)
        else 
            wait(RunSem, !IO),
            set_running(no, !IO),
            signal(RunSem, !IO)
    ).
   

:- pred input(semaphore::in, semaphore::in, thread::in, io::di, io::uo) is cc_multi.
input(CmdSem, RunSem, Thread, !IO):-
    %write_string("call input\n", !IO),
    read_line(Res, !IO),
    (ok(TmpList) = Res -> TmpList = List ; error("broken input")),
    from_char_list(List, Cmd),
    wait(CmdSem, !IO),
    set_cmd(Cmd,!IO),
    signal(CmdSem, !IO),
    %write_string("read " ++ Cmd, !IO),
    %nl(!IO),
    wait(RunSem, !IO),
    get_running(Call, !IO),
    signal(RunSem, !IO),
    (
        if  Call = yes  then
            input(CmdSem, RunSem, Thread, !IO)
        else
            true
    ).

:- pred call_engine(string::in, bool::out, io::di, io::uo) is det.
call_engine(String, Next, !IO):-
    Cmds = words_separator(char.is_whitespace, String),
    length(Cmds, Num),
    get_enst(Enst0, !IO),
    (
        if
            Num = 0
        then
            %write_string("call call_tick\n", !IO),
            call_tick(Enst0, Enst, Next, !IO)
            %write_string("call_tick ended\n", !IO)
        else
            det_index0(Cmds, 0, Cmd),
            (
                if Cmd = "usi"  then
                    call_usi(Enst,!IO),
                    Next = yes
                else if Cmd = "isready" then
                    engine.isready(Enst0, Enst, !IO), Next = yes, write_string("readyok\n", !IO)
                else if Cmd = "setoption" then
                    call_setoption(Cmds, Enst0, Enst), Next = yes
                else if Cmd = "usinewgame"  then
                    engine.usinewgame(Enst0, Enst), Next = yes
                else if Cmd = "position"    then
                    (call_position(Cmds, Enst0, TmpEnst) -> TmpEnst = Enst, Next = yes /*,write(Enst ^ engine.curr_state, !IO)*/ ; write_string("position failed. Engine will stop.\n", !IO), Enst = Enst0, Next = no)
                else if Cmd = "go"  then
                    /*write_string("call call_go\n", !IO),*/ call_go(Cmds, Enst0, Enst, !IO), Next = yes
                else if Cmd = "stop"    then
                    engine.stop(Enst0, Enst), Next = yes
                else if Cmd = "ponderhit"   then
                    call_ponderhit(Enst0, Enst, !IO), Next = yes
                else if Cmd = "quit"    then
                    engine.quit(Enst0, Enst), Next = yes
                else if Cmd = "gameover"    then
                    (call_gameover(Cmds, Enst0, TmpEnst) -> TmpEnst = Enst, Next = yes ; Enst0 = Enst, Next = no)
                else
                    Enst0 = Enst,
                    Next = yes,
                    write_string("Unknown command.\n", !IO)
            )
    ),
    flush_output(!IO),
    set_enst(Enst, !IO).

:- pred call_usi(engine.enst::engine.enst_out, io::di, io::uo) is det.
call_usi(Enst, !IO):-
    engine.usi(Program, Auther, Options, Enst),
    write_string("id name " ++ Program ++ "\n", !IO),
    write_string("id author " ++ Auther ++ "\n", !IO),
    write_options(Options, !IO),
    write_string("usiok\n", !IO).

:- pred write_options(list({string, usi.option_type})::in, io::di, io::uo) is det.
write_options([{Name, Type} | L], !IO):-
    write_string("option name " ++ Name ++ " type " ++ string(Type) ++ "\n", !IO),
    write_options(L,!IO).
write_options([], !IO).

:- pred call_tick(engine.enst::engine.enst_di, engine.enst::engine.enst_out, bool::out, io::di, io::uo) is det.
call_tick(Enstin, Enstout, Succ, !IO):-
    clock(Now, !IO),
    %write_string("call engine.tick\n", !IO),
    engine.tick(Now, Info, BestMove, PonderMove, Enstin, Enstout, !IO, Succ),
    %write_string("engine.tick ended\n", !IO),
    write_info(Info, !IO),
    (
        if  BestMove \= maybe.no
        then
            (yes(BestMove1) = BestMove -> BestMove0 = BestMove1 ; error("bestmove internal error")),
            write_string("bestmove " ++ sfen.move(BestMove0), !IO),
            (
                if  PonderMove \= maybe.no
                then
                    (yes(PonderMove1) = PonderMove -> PonderMove0 = PonderMove1 ; error("pondermove internal error")),
                    write_string(" ponder " ++ sfen.move(PonderMove0), !IO)
                else
                    true
            ),
            nl(!IO)
        else
            true
    ).

:- pred write_info(usi.info::in, io::di, io::uo) is det.
write_info(usi.info(Depth, Seldepth, Time, Nodes, Pv, Cp, Mate, Currmove, Hashfull, Nps),!IO):-
    (
        if  Depth = yes(Depth0) then
            write_string("depth ", !IO),
            write_int(Depth0, !IO),
            (
                if  Seldepth = yes(Seldepth0) then
                    write_string(" seldepth ", !IO),
                    write_int(Seldepth0, !IO)
                else
                    true
            ),
            write_string(" ", !IO)
        else
            true
    ),
    (
        if  Time = yes(Time0) then
            write_string("time ", !IO),
            write_int(Time0, !IO),
            write_string(" ", !IO)
        else
            true
    ),
    (
        if  Nodes = yes(Nodes0) then
            write_string("nodes ", !IO),
            write_int(Nodes0, !IO),
            write_string(" ", !IO)
        else 
            true
    ),
    (
        if  Cp = yes(Cp0)   then
            write_string("score cp ", !IO),
            write_int(Cp0, !IO),
            write_string(" ", !IO)
        else if Mate = yes(Mate0)   then
            write_string("score mate ", !IO),
            write_int(Mate0, !IO),
            write_string(" ", !IO)
        else
            true
    ),
    (
        if  Currmove = yes(Currmove0)   then
            write_string("currmove " ++ sfen.move(Currmove0) ++ " ", !IO)
        else
            true
    ),
    (
        if  Hashfull = yes(Hashfull0) then
            write_string("hashfull ", !IO),
            write_int(Hashfull0, !IO),
            write_string(" ", !IO)
        else
            true
    ),
    (
        if  Nps = yes(Nps0) then
            write_string("nps ", !IO),
            write_int(Nps0, !IO),
            write_string(" ", !IO)
        else 
            true
    ),
    (
        if  Pv = yes(Pv0)   then
            write_string("pv ", !IO),
            write_pv(Pv0, !IO)
        else
            true
    ),
    (
        if
            Depth = no,
            Time = no,
            Nodes = no,
            Pv =no,
            Cp = no,
            Mate = no,
            Currmove = no,
            Hashfull = no,
            Nps = no
        then 
            true
        else
            nl(!IO)
    ).

:- pred write_pv(list(stype.move)::in, io::di, io::uo) is det.
write_pv([Move | L], !IO):-
    write_string(sfen.move(Move) ++ " ", !IO),
    write_pv(L, !IO).
write_pv([], !IO).

:- pred call_setoption(list(string)::in, engine.enst::engine.enst_di, engine.enst::engine.enst_out) is det.
call_setoption(Options,EnstIn,EnstOut):-
    (
        if  Options = [_,_,Name,_,Value]    then
            engine.setoption(Name, Value, EnstIn, EnstOut)
        else
            error("setoption unknown format")
    ).


:- pred call_position(list(string)::in, engine.enst::engine.enst_di, engine.enst::engine.enst_out) is semidet.
call_position([_ | [Sfen | Pos]], EnstIn, EnstOut):-
    (
        if Sfen = "startpos" then
            sfen.pos(Sfen, Pos0),
            Turn0 = stype.b
        else 
            error("startiing from arbituraly position is not supported.")
    ),
    (
        if
            index1_of_first_occurrence(Pos, "moves", N)
        then
            split_list(N, Pos, _, SfenMoves)
        else
            SfenMoves = []
    ),
    engine.position(Pos0, Turn0, SfenMoves, EnstIn, EnstOut).

:- pred call_go(list(string)::in, engine.enst::engine.enst_di, engine.enst::engine.enst_out, io::di, io::uo) is det.
call_go(GoString, EnstIn, EnstOut, !IO):-
    %write_string("start call_go\n", !IO),
    clock(Now, !IO),
    %write_string("unify Gostring to [_|OpStr]\n", !IO),
    (GoString =  [_ | OpStr] -> OptionString = OpStr ; error("go option internal error")),
    %write_string("call read_options\n", !IO),
    read_options(OptionString, Option),
    %write_string("call engine.go\n", !IO),
    engine.go(Option, Now, EnstIn, EnstOut, !IO).
    %write_string("engine.go ended\n", !IO).

:- pred read_options(list(string)::in, usi.options::out) is det.
read_options(StringList, Options):-
    read_options_rec(StringList, usi.options(no, 0, 0, 0, 0, 0, no, 0), Options).
:- pred read_options_rec(list(string)::in, usi.options::in, usi.options::out) is det.
read_options_rec([OptionString | L], Old, Options):-
    (
        if  OptionString = "ponder" then
            Tmp = Old ^ usi.ponder := yes,
            read_options_rec(L, Tmp, Options)
        else if OptionString = "btime"  then
            det_index0(L, 0, Btimestr),
            det_index0(L, 2, Wtimestr),
            (split_list(3, L, _, Tail0),
            to_int(Btimestr, Btime0),
            to_int(Wtimestr, Wtime0) ->
            Tail = Tail0, Btime0 = Btime, Wtime0 = Wtime ;
            error("Unsupported go option format.")),
            Tmp = (Old ^ usi.btime := Btime) ^ usi.wtime := Wtime,
            read_options_rec(Tail, Tmp, Options)
        else if OptionString = "byoyomi"    then
            (L = [TimeStr | Tail0],
            to_int(TimeStr, Byoyomi0) ->
            Tail = Tail0, Byoyomi = Byoyomi0 ;
            error("Byoyomi was given but time not specified as int.")),
            Tmp = Old ^ usi.byoyomi := Byoyomi,
            read_options_rec(Tail, Tmp, Options)
        else if OptionString = "binc"   then
            det_index0(L, 0, BincStr),
            det_index0(L, 2, WincStr),
            (split_list(3, L, _, Tail0),
            to_int(BincStr, Binc0),
            to_int(WincStr, Winc0) ->
            Tail = Tail0, Binc = Binc0, Winc = Winc0 ;
            error("binc and winc not given correctly")),
            Tmp = (Old ^ usi.binc := Binc) ^ usi.winc := Winc,
            read_options_rec(Tail, Tmp, Options)
        else if OptionString = "infinite"   then
            Tmp = Old ^ usi.infinite := yes,
            read_options_rec(L, Tmp, Options)
        else if OptionString = "mate"   then
            (L = [Mate0 | _] -> Mate = Mate0 ; error("mate given but time not specified.")),
            (
                if  Mate = "infinite"   then
                    Options = Old ^ usi.mate := -1
                else
                    (to_int(Mate, Time0) -> Time = Time0 ; error("mate time was neither infinite nor int.")),
                    Options = Old ^ usi.mate := Time
            )
        else
            error("Unknown go option.")
    ).
read_options_rec([], Options, Options).

:- pred call_ponderhit(engine.enst::engine.enst_di, engine.enst::engine.enst_out, io::di, io::uo) is det.
call_ponderhit(EnstIn, EnstOut, !IO):-
    clock(Now, !IO),
    engine.ponderhit(Now, EnstIn, EnstOut).

:- pred call_gameover(list(string)::in, engine.enst::engine.enst_di, engine.enst::engine.enst_out) is semidet.
call_gameover([ResultString], EnstIn, EnstOut):-
    read_from_string("gameover", ResultString, length(ResultString), ok(Result), io.posn(0,0,0),_),
    engine.gameover(Result, EnstIn, EnstOut).