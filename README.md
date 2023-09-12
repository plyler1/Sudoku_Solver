# Sudoku_Solver
An A.I. project I did to automatically solve Sudoku boards.

Most of the files for the project were given except for the BTSolver file. This file has user-defined functions which I have made to solve the boards with varying heuristics.
Heuristics such as forward checking, minimum remaining value with and without tie breaker, and least constraining value were implemented. Constraint propagation and consistency checking were also done within these algorithms. Norvig's heuristic, which is described in this article: https://norvig.com/sudoku.html, was done using a combination of these heuristics.
