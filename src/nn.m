:- module nn.
:- interface.
:- import_module io, maybe, list, array.

:- type nn. %abstruct
:- type vect(T)
    --->   sparse(
        size::int,
        zero::T,
        vals::list({int, T})
    )
    ;   dense(array.array(T)).

:- pred load(string::in, maybe_error(nn)::out, io::di, io::uo) is det.
:- pred unsafe_forward(nn::in, vect(float)::in, vect(float)::out) is det.
:- pred unsafe_at(nn.vect(T)::in, int::in, T::out) is det.
:- func make_empty = nn is det.

:- implementation.
:- import_module int,float,char,string.

:- type layer
    ---> sensor
    ;   hidden
    ;   output.
:- type node
    ---> node(
        layer::nn.layer,
        input::list(nn.handle),
        weights::vect(float),
        activation::pred(float::in, float::out) is det
    ).
:- type handle %handle to a node
    --->    handle(int).
:- type nn
    ---> nn(
        num_sensor::int,
        num_hidden::int,
        num_output::int,
        nodes::array(node)
    ).

:- pred relu(float::in, float::out) is det.
relu(X, max(0.0, X)).
:- pred id(float::in, float::out) is det.
id(X, X).

load(File, NN, !IO):-
    read_named_file_as_string(File, Res, !IO),
    (
        if
            Res = ok(String)
        then
            (
                if  nn.from_string(String, NN0) then
                    NN = ok(NN0)
                else
                    NN = error("Could not load model.")
            )
        else
            NN = error("Could not open model file.")
    ).

:- pred from_string(string::in, nn::out) is semidet.
from_string(String, NN):-
    string.words_separator(char.is_whitespace, String) = StringList,
    list.index0_of_first_occurrence(StringList, "connections", N),
    list.split_list(N, StringList, [_|Nodes], [_|Connections]),
    nn.read_nodes(Nodes, nn.make_empty, NN0),
    nn.read_connections(Connections, NN0, NN).

:- pred read_nodes(list(string)::in, nn::in, nn::out) is semidet.
read_nodes([LayerStr|[LocalStr|[_|StringList]]], nn(Sens0, Hid0, Out0, Nodes0), NN):-
    io.read_from_string("layername",LayerStr++".",7,ok(Layer),io.posn(0,0,0),_),
    string.to_int(LocalStr, Local),
    (
        if  Layer = nn.sensor   then
            Sensor = Sens0 + 1,
            Hidden = Hid0,
            Output = Out0,
            Act = nn.id
        else if Layer = nn.hidden   then
            Sensor = Sens0,
            Hidden = Hid0 + 1,
            Output = Out0,
            Act = nn.relu
        else
            Sensor = Sens0,
            Hidden = Hid0,
            Output = Out0 + 1,
            Act = nn.id
    ),
    Node = node(Layer, [], nn.init_dense(0, 0.0), Act),
    nn.safe_set(Local, Node, Nodes0, Nodes),
    NN1 = nn.nn(Sensor, Hidden, Output, Nodes),
    read_nodes(StringList, NN1, NN).
read_nodes([], NN, NN).

:- pred read_connections(list(string)::in, nn::in, nn::out) is semidet.
read_connections([_|[_|[InStr|[_|[OutStr|[WeightStr|["true"|StringList]]]]]]], NN0, NN):- 
    string.to_int(InStr, In),
    string.to_int(OutStr, Out),
    string.to_float(WeightStr, Weight),
    NN0 ^ nodes = Nodes0,
    array.lookup(Nodes0, Out, OutNode0),
    Inputs0 = OutNode0 ^ input,
    dense(Weights0) = OutNode0 ^ weights,
    list.append(Inputs0, [nn.handle(In)], Inputs),
    Weights = dense(append(Weights0, array.init(1, Weight))),
    OutNode = (OutNode0 ^ input := Inputs) ^ weights := Weights,
    array.unsafe_set(Out, OutNode, Nodes0, Nodes),
    NN1 = NN0 ^ nodes := Nodes,
    read_connections(StringList, NN1, NN).
read_connections([_|[_|[_|[_|[_|[_|["false"|StringList]]]]]]], NN0, NN):- 
    read_connections(StringList, NN0, NN).
read_connections([], NN, NN).

unsafe_forward(NN, In, Out):-
    nn.num_nodes(NN, NodeNum),
    array.init(NodeNum, maybe.no, Memo),
    nn.output_nodes(NN, OutNodes),
    nn.unsafe_compute_all(NN, OutNodes, In, Out, Memo, _).

:- pred to_int(handle::in, int::out) is det.
:- func to_int(handle) = int.
to_int(handle(H), H).
to_int(H) = N :- to_int(H,N).


:- pred unsafe_compute(nn::in, nn.handle::in, vect(float)::in, float::out, array(maybe(float))::array_di, array(maybe(float))::array_uo) is det.
unsafe_compute(NN, Handle, X, Ans, !Memo) :-
    nn.unsafe_get_node(NN, Handle, Node),
    (
        if
            unsafe_lookup(!.Memo, nn.to_int(Handle), yes(Ans0))
        then
            Ans = Ans0
        else
        (
            if  Node ^ layer = nn.sensor    then
                nn.unsafe_at(X, to_int(Handle), Ans1),
                call(Node ^ activation, Ans1, Ans)
            else
                nn.unsafe_compute_all(NN, Node ^ nn.input, X, Input, !Memo),
                unsafe_dot(Input, Node ^ weights, Ans1),
                call(Node ^ activation, Ans1, Ans)
        ),
        unsafe_set(to_int(Handle), yes(Ans), !Memo)
    ).

:- pred unsafe_compute_all(nn::in, list(nn.handle)::in, vect(float)::in, vect(float)::out, array(maybe(float))::array_di, array(maybe(float))::array_uo) is det.
unsafe_compute_all(NN, Handles, X, Ans, !Memo):-
    unsafe_compute_all_rec(NN, Handles, 0, X, init_dense(length(Handles), 0.0), Ans, !Memo).

:- pred unsafe_compute_all_rec(nn::in, list(nn.handle)::in, int::in, vect(float)::in, vect(float)::in, vect(float)::out, array(maybe(float))::array_di, array(maybe(float))::array_uo) is det.
unsafe_compute_all_rec(NN, [Handle|L], Index, X, Init, Ans, !Memo):-
    nn.unsafe_compute(NN, Handle, X, Y, !Memo),
    nn.unsafe_compute_all_rec(NN, L, Index+1, X, Init, Ans0, !Memo),
    nn.unsafe_set(Index, Y, Ans0, Ans).
unsafe_compute_all_rec(_, [], _, _, Ans, Ans, !Memo).

:- pred num_nodes(nn::in, int::out) is det.
num_nodes(NN, NN ^ num_sensor + NN ^ num_hidden + NN ^ num_output).

:- pred output_nodes(nn::in, list(handle)::out) is det.
output_nodes(NN, Nodes):-
    First = NN ^ num_sensor + NN ^ num_hidden,
    create_handles(First, First + NN ^ num_output, Nodes).

:- pred create_handles(int::in, int::in, list(handle)::out) is det.
create_handles(First, Upper, Handles) :- create_handles_rec(First, Upper, [], Handles).

:- pred create_handles_rec(int::in, int::in, list(handle)::in, list(handle)::out) is det.
create_handles_rec(Idx, Upper, List, Handles):-
(
    if  Idx < Upper   then
        append(List, [handle(Idx)], Tmp),
        create_handles_rec(Idx+1, Upper, Tmp, Handles)
    else 
        List = Handles
).

:- pred safe_set(int::in, nn.node::in, array(nn.node)::array_di, array(nn.node)::array_uo) is semidet.
safe_set(Index, Node, !Array):-
    0 =< Index,
    Index - array.max(!.Array) = Diff,
    (
        if  0 < Diff  then
            !:Array = append(!.Array, array.init(Diff, nn.node(nn.hidden,[],nn.init_dense(0,0.0),nn.relu)))
        else
            true
    ),
    array.unsafe_set(Index, Node, !Array).

:- pred make_empty(nn::out) is det.
make_empty(nn.nn(0,0,0,array.make_empty_array)).
make_empty = NN :- make_empty(NN).

:- pred unsafe_get_node(nn::in, handle::in, node::out) is det.
unsafe_get_node(NN, handle(Handle), Node):-
    unsafe_lookup(NN ^ nodes, Handle, Node).

:- pred init_dense(int::in, T::in, vect(T)::out) is det.
:- func init_dense(int::in, T::in) = (vect(T)::out) is det.
init_dense(Size, Value, Vect):-
    array.init(Size, Value, Array),
    Vect = nn.dense(Array).
init_dense(Size, Value) = Vect :-
    init_dense(Size, Value, Vect).

unsafe_at(dense(Array), Index, Value):-
    unsafe_lookup(Array, Index, Value).
unsafe_at(sparse(Size, Zero, [{Idx0,Val0} | L]), Index, Value):-
    (
        if  Idx0 = Index    then
            Value = Val0
        else
            unsafe_at(sparse(Size, Zero, L), Index ,Value)
    ).
unsafe_at(sparse(_, Zero, []), _, Zero).

:- pred unsafe_set(int::in, float::in, vect(float)::in, vect(float)::out) is det.
unsafe_set(Index, Value, dense(Array0), dense(Array1)):-
    array.unsafe_set(Index, Value, Array0, Array1).
unsafe_set(Index, Value, sparse(Size, Zero, List0), sparse(Size, Zero, List)):-
    (remove({Index, 0.0}, List0, List01) -> List1 = List01 ; List1 = List0),
    append(List1, [{Index, Value}], List).

:- pred remove({int, float}::in, list({int, float})::in, list({int, float})::out) is semidet.
remove({X, _}, [{A, A1}|L], M):-
    (
        if  X = A   then
            L = M
        else
            M = [{A, A1}|B],
            remove({X, 0.0}, L, B)
    ).


:- pred unsafe_dot(vect(float)::in, vect(float)::in, float::out) is det.
unsafe_dot(dense(ArrayA), dense(ArrayB), Product) :-
    unsafe_dot_array(ArrayA, ArrayB, max(ArrayA), 0, 0.0, Product).
unsafe_dot(sparse(_, _, Sparse), Vect, Product) :-
    unsafe_dot_sparse(Sparse, Vect, 0.0, Product).
unsafe_dot(dense(A), sparse(B1,B2,B3), Product) :- unsafe_dot(sparse(B1,B2,B3), dense(A), Product).

:- pred unsafe_dot_array(array(float)::in, array(float)::in, int::in, int::in, float::in, float::out) is det.
unsafe_dot_array(ArrayA, ArrayB, Max, Index, Acc, Product):-
    (
        if  Index =< Max    then
            (unsafe_lookup(ArrayA, Index, A)&
            unsafe_lookup(ArrayB, Index, B)),
            unsafe_dot_array(ArrayA, ArrayB, Max, Index+1, Acc+A*B, Product)
        else
            Acc = Product
    ).

:- pred unsafe_dot_sparse(list({int, float})::in, vect(float)::in, float::in, float::out) is det.
unsafe_dot_sparse([{Index, A} | L], Vect, Acc, Product):-
    nn.unsafe_at(Vect, Index, B),
    unsafe_dot_sparse(L, Vect, Acc+A*B, Product).
unsafe_dot_sparse([], _, Product, Product).
