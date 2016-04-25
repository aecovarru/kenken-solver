% This predicate solves a KenKen game
% Each column and row must contain integers 1 to N
% Each contraint must be satisfied
% N is the length of one side of square board
% C is a list of constraints
% T is a list of integers from 1 to N

% reordered goal using length for use in the maplist function
revLength(N, Tlist) :- length(Tlist, N).

% goal used to set the domain of each list in T
listDomain(N, Tlist) :- fd_domain(Tlist, 1, N).

% constraint helper functions
constraints(T, Celem) :- findConstraint(T, Celem).

% find constraint that matches with the syntax provided and call corresponding predicate
findConstraint(T, +(S, L)) :- add(T, S, L, 0).
findConstraint(T, *(P, L)) :- multiply(T, P, L, 1).
findConstraint(T, -(D, J, K)) :- subtract(T, D, J, K).
findConstraint(T, /(Q, J, K)) :- divide(T, Q, J, K).

% find element in table using the indices provided
findElem(T, I_index-J_index, Element) :- nth(I_index, T, Row), nth(J_index, Row, Element).

% work predicates all contain a base case that checks equality and a recursive predicate that does work
add(_, S, [], S).
add(T, S, [Head|Tail], Accum) :-
	findElem(T, Head, Elem),
	RecursiveAccum #= Accum + Elem,
	add(T, S, Tail, RecursiveAccum).

multiply(_, P, [], P).
multiply(T, P, [Head|Tail], Accum) :-
	findElem(T, Head, Elem),
	RecursiveAccum #= Accum * Elem,
	multiply(T, P, Tail, RecursiveAccum).

% base case has spot for Accum and there are two options for subtraction so we need two predicates
subtract(_, D, _, _, D).
subtract(T, D, J, K) :-
	findElem(T, J, Elem1),
	findElem(T, K, Elem2),
	Accum #= Elem1 - Elem2,
	subtract(T, D, J, K, Accum).
subtract(T, D, J, K) :-
	findElem(T, K, Elem1),
	findElem(T, J, Elem2),
	Accum #= Elem1 - Elem2,
	subtract(T, D, J, K, Accum).

% same goes for division as subtraction
divide(_, Q, _, _, Q).
divide(T, Q, J, K) :-
	findElem(T, J, Elem1),
	findElem(T, K, Elem2),
	Accum #= Elem1 / Elem2,
	divide(T, Q, J, K, Accum).
divide(T, Q, J, K) :-
	findElem(T, K, Elem1),
	findElem(T, J, Elem2),
	Accum #= Elem1 / Elem2,
	divide(T, Q, J, K, Accum).

% used the implementation of transpose used in SWI
transpose([], []).
transpose([F|Fs], Ts) :-
    transpose(F, [F|Fs], Ts).

transpose([], _, []).
transpose([_|Rs], Ms, [Ts|Tss]) :-
        lists_firsts_rests(Ms, Ts, Ms1),
        transpose(Rs, Ms1, Tss).

lists_firsts_rests([], [], []).
lists_firsts_rests([[F|Os]|Rest], [F|Fs], [Os|Oss]) :-
        lists_firsts_rests(Rest, Fs, Oss).


kenken(N, C, T) :-
	% set the size of the NxN array and the domain of each list in T from 1 to N
	length(T, N), maplist(revLength(N), T), maplist(listDomain(N), T),
	% take care of constraints in C using helper functions defined above
	maplist(constraints(T), C),
	% make sure every element in each row and column in T is unique
	maplist(fd_all_different, T), transpose(T, Transpose), maplist(fd_all_different, Transpose),
	% make sure each element in T is assigned a value
	maplist(fd_labeling, T).


% used to create domain for the plain table
plainDomain(N, L) :- findall(Counter, between(1, N, Counter), L).

% recursive non finite domain solver method that checks if all elements are unique
nonFiniteAllDifferent([]).
nonFiniteAllDifferent([Head|Tail]) :- \+(member(Head, Tail)), nonFiniteAllDifferent(Tail).


plain_kenken(N, C, T) :-
	% set the size of the NxN array
	length(T, N), maplist(revLength(N), T),
	% sets all the possible domains for the plain_kenken
	plainDomain(N, L), maplist(permutation(L), T),
	% make sure every elementin the column in T is unique, no need to check rows since permutation took care of that
	transpose(T, Transpose), maplist(fd_all_different, Transpose),
	% in this inefficient implementation, we check the constraints after we find a valid domain
	% use the plain implemenation of the constraints
	maplist(plainConstraints(T), C).
	


% plainConstraint helper functions
plainConstraints(T, Celem) :- findPlainConstraint(T, Celem).

% find constraint that matches with the syntax provided and call corresponding predicate
findPlainConstraint(T, +(S, L)) :- plainAdd(T, S, L, 0).
findPlainConstraint(T, *(P, L)) :- plainMultiply(T, P, L, 1).
findPlainConstraint(T, -(D, J, K)) :- plainSubtract(T, D, J, K).
findPlainConstraint(T, /(Q, J, K)) :- plainDivide(T, Q, J, K).


% for plain constraints, use is rather than fd_domain arithmetic assignment

% work predicates all contain a base case that checks equality and a recursive predicate that does work
plainAdd(_, S, [], S).
plainAdd(T, S, [Head|Tail], Accum) :-
	findElem(T, Head, Elem),
	RecursiveAccum is Accum + Elem,
	plainAdd(T, S, Tail, RecursiveAccum).

plainMultiply(_, P, [], P).
plainMultiply(T, P, [Head|Tail], Accum) :-
	findElem(T, Head, Elem),
	RecursiveAccum is Accum * Elem,
	plainMultiply(T, P, Tail, RecursiveAccum).

% base case has spot for Accum and there are two options for subtraction so we need two predicates
plainSubtract(_, D, _, _, D).
plainSubtract(T, D, J, K) :-
	findElem(T, J, Elem1),
	findElem(T, K, Elem2),
	Accum is Elem1 - Elem2,
	plainSubtract(T, D, J, K, Accum).
plainSubtract(T, D, J, K) :-
	findElem(T, K, Elem1),
	findElem(T, J, Elem2),
	Accum is Elem1 - Elem2,
	plainSubtract(T, D, J, K, Accum).

% same goes for division as subtraction
plainDivide(_, Q, _, _, Q).
plainDivide(T, Q, J, K) :-
	findElem(T, J, Elem1),
	findElem(T, K, Elem2),
	Accum is Elem1 / Elem2,
	plainDivide(T, Q, J, K, Accum).
plainDivide(T, Q, J, K) :-
	findElem(T, K, Elem1),
	findElem(T, J, Elem2),
	Accum is Elem1 / Elem2,
	plainDivide(T, Q, J, K, Accum).




% Analysis
% When using kenken on the puzzle with multiple solutions and measuring performance with statistics
% Measurements:
% User Time - 0.004 seconds
% System Time - 0.004 seconds
% CPU Time - 0.008 seconds
% Real Time - 6.408 seconds

% When using plain_kenken on the same test case as above
% Measurements:
% User Time - 0.692 seconds
% System Time - 0.008 seconds
% CPU Time - 0.700 seconds
% Real Time - 30.109 seconds

% Conclusion, plain_kenken must try more test cases than kenken thus making plain_kenken less efficient.


% No-Op API
% Given a puzzle with only target numbers,
% Pass in an argument of the length of a side of the square grid N.
% Pass in a list of constraints of this form.
% operand(Num, List)
% where operand is the operation the kenken game must perform, Num is the value after the operation
% has been performed to the list of squares in List. Division and subtraction should only have
% two elements in the list. A constraint val(Num, List) assigns all squares in List that value Num.
% Last but not least, pass in a variable that stores the solution of the No-Op Kenken solver.
% If no solution is returned, then either not every element in the table had a corresponding rule,
% or there is no possible solution to this no-op kenken. If a solution is returned, type ;
% to see if any other solutions are possible.

% Example call for No-Op KenKen Solver
% No_op_kenken(2, [+(5, [1-1, 1-2, 2-1]), val(1, [2-2])], T).