# OCaml Regex Engine

This repository contains two OCaml modules for working with finite automata. These modules provide functionality for creating and manipulating non-deterministic finite automata (NFAs) and for converting regular expressions to NFAs.

## Modules

## NFA

The `NFA` module provides a set of functions and types for creating and working with NFAs. It includes the following main features:

- Definition of NFA structure with states, alphabet, transitions, initial state, and final states.
- Functions for NFA operations such as transition state calculation, epsilon closure computation, and string acceptance checking.
- Utility functions for converting a string to a character list.
- Implementation of the subset construction algorithm for converting an NFA to a deterministic finite automaton (DFA).

## Regex

The `Regex` module focuses on regular expressions and their conversion to NFAs. Key features include:

- Definition of regular expression types, including empty string, character, union, concatenation, and repetition.
- Functions to convert regular expressions to NFAs, following the standard algorithms.
- Tokenizer and parser implementations for converting a string representation of a regular expression into its structured form.
