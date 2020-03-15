node(X,Y,N) :-
  (abs(X) + abs(Y)) =< (2 * N),
  (abs(Y)) =< N,
  (abs(X) + abs(Y)) >= 1,
  mod(X,2) =:= mod(Y,2).

all_nodes(X, Y, N) :- 
  A1 is 2*N,
  B1 is -2*N,
  A2 is N,
  B2 is -N,
  between(B1, A1, X), 
  between(B2, A2, Y),
  node(X,Y,N).

all_nbrs(X, Y, X1,Y1, N, Visited) :- 
  A1 is X+2,
  B1 is X-2,
  A2 is Y+1,
  B2 is Y-1,
  between(B1, A1, X1), 
  between(B2, A2, Y1),
  (X =:= X1 -> (Y =\= Y1); 1<2),
  (member((X1,Y1,_),Visited) -> (1 > 2) ; 1<2),
  node(X1,Y1,N).

%% print_list([]) :-
%%   format('~n',[]).

%% print_list([H|T]) :-
%%   format('~w|',[H]),
%%   print_list(T).
  
list_nodes(L, N) :-
  findall((X, Y), all_nodes(X, Y, N), L).

list_nbrs((X,Y), L, N, Visited) :-
  findall((X1, Y1), all_nbrs(X, Y, X1,Y1, N, Visited), L).

dfs_list([H|T],V,Visited, Pre_filled, Links, Result, N, N1) :-
  dfs(H,V,Visited,Pre_filled,Links,Result,N, N1);
  dfs_list(T,V,Visited, Pre_filled, Links, Result, N, N1).


dfs((X,Y),V,Visited, Pre_filled, _, Result, _, N1) :-
    (member((X,Y,V2),Pre_filled) -> V2 =:= V; 1 < 2),
    V =:= (N1-1),
    Result = [(X,Y,V)|Visited].

dfs((X,Y),V,Visited, Pre_filled, Links, Result, N, N1) :-
  V1 is (V+1),
  (member((T,U,V),Pre_filled) -> ((T =:= X),(U =:= Y)); 1 < 2), 
  (member((X,Y,V2),Pre_filled) -> V2 =:= V; 1 < 2),
  list_nbrs((X,Y), L, N, [(X,Y,V)|Visited]),
  ((member((X,Y,X1,Y1),Links);
    member((X1,Y1,X,Y),Links)) -> 
    (member((X1,Y1,_),Visited) -> 
      dfs_list(L, V1, [(X,Y,V)|Visited], Pre_filled, Links, Result, N, N1);
      dfs((X1,Y1),V1,[(X,Y,V)|Visited], Pre_filled, Links, Result, N, N1));
    dfs_list(L, V1, [(X,Y,V)|Visited], Pre_filled, Links, Result, N, N1)).

  rikudo(N, Pre_filled, Links, Result) :-
    set_prolog_flag(answer_write_options,
                   [ quoted(true),
                     portray(true),
                     spacing(next_argument)
                   ]),
    (N =:= 7 -> N1 = 1; 1<2),
    (N =:= 19 -> N1 = 2; 1<2),
    (N =:= 37 -> N1 = 3; 1<2),
    (N =:= 61 -> N1 = 4; 1<2),
    (N =:= 91 -> N1 = 5; 1<2),
    (N =:= 127 -> N1 = 6; 1<2),
    list_nodes(L, N1),
    (member((X,Y,1),Pre_filled) -> dfs((X,Y),1,[(0,0,-10)],Pre_filled,Links,Result,N1, N) ; dfs_list(L, 1, [(0,0,-10)], Pre_filled, Links, Result, N1, N)).
