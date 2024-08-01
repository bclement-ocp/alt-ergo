# Model generation

Alt-Ergo can generate best-effort models (also known as counter-examples in
the program verification community) in the case it cannot conclude the
unsatisfiability of the context.

Model generation is supported in all input languages, but more functionality is
available when using the SMT-LIB input language.

```{note}
Generated models are always displayed using SMT-LIB syntax, even when using the
native input language.
```

## Activation

Model generation is disabled by default and needs to be enabled before being
used. There are multiple ways to enable model generation:

 - With the SMT-LIB language, using either `(set-option :produce-models true)`
   in a script, or with the `--produce-model` option. This enables the use of
   the `(check-sat)` command defined in the SMT-LIB standard.

 - With the native language, using the `--dump-models` option. This will cause
   Alt-Ergo to automatically (try to) produce a model after each `check_sat`
   statement that returns `I don't know`, and a counter-example after each
   `goal` statement that cannot be proven `Valid`.

## Correctness of model generation

Alt-ergo's model generation procedure is incomplete in the presence of
quantifiers, and hence Alt-ergo only ever produces candidate models that are
not guaranteed to satisfy all the assertions in the problem. *Ground*
assertions (i.e. assertions that do not involve quantifiers) are guaranteed to
hold in the models generated by Alt-ergo as long as they only include the
following constructs:

 - Boolean connectives;

 - Algebraic data types (including records and enumerated types in the native
   language)

 - Integer and real primitives (addition, subtraction, multiplication,
   division, modulo, exponentiation, and comparisons), but not conversion
   operators between reals and integers

 - Bit-vector primitives (concatenation, extraction, `bvadd`, `bvand`, `bvule`,
   etc.), including `bv2nat` and `int2bv`

Completeness for the following constructs is only guaranteed with certain
command-line flags:

 - Conversions operators between integers and reals require the
   `--enable-theories ria` flag

 - Floating-point primitives (`ae.round`, `ae.float32` etc. in the SMT-LIB
   language; `float`, `float32` and `float64` in the native language) require
   the `--enable-theories fpa` flag

Model generation is known to be sometimes incomplete in the presence of arrays.

## Examples

  - Using the native language in the input file `INPUT.ae`:

  ```
    logic a, b, c : int
    axiom A : a <> c

    check_sat c1: a = b + c
    check_sat c2: a <> b
  ```
  and the command `alt-ergo --dump-models INPUT.ae`, Alt-Ergo produces the
  output models:

  ```
    ; Model for c1
    (
      (define-fun a () Int 2)
      (define-fun b () Int 2)
      (define-fun c () Int 0)
    )
    I don't known

    ; Model for c2
    (
      (define-fun a () Int 2)
      (define-fun b () Int 0)
      (define-fun c () Int 0)
    )
    I don't known
  ```

  ```{admonition} Note

  In this example the model for the statement `check_sat c2` is not a
  model for the statement `check_sat c1` since `check_sat` are independent in
  the native language. The same goes for `goals`.

  ```

  - Using the SMT-LIB language in the input file `INPUT.smt2`:

  ```
    (set-logic ALL)
    (declare-fun a () Int)
    (declare-fun b () Int)
    (declare-fun c () Int)

    (assert (= a (+ b c)))
    (check-sat)
    (get-model)

    (assert (distinct a b))
    (check-sat)

  ```
  and the command `alt-ergo --produce-models INPUT.smt2` produces the output
  ```
    unknown
    (
      (define-fun a () Int 0)
      (define-fun b () Int 0)
      (define-fun c () Int 0)
    )

    unknown
  ```

  ```{admonition} Note

  There is no model printed after the second `(check-sat)` since we
  don't demand it with the statement `(get-model)`.
  ```


  - Alternatively, using the statement `(set-option :produce-models true)`
  ```
   (set-logic ALL)
   (set-option :produce-models true)
   (declare-fun a () Int)
   (declare-fun b () Int)
   (declare-fun c () Int)

   (assert (= a (+ b c)))
   (check-sat)
   (get-model)

  ```
  and the command `alt-ergo INPUT.smt2` produces
  the output model
  ```
  unknown
  (
    (define-fun a () Int 0)
    (define-fun b () Int 0)
    (define-fun c () Int 0)
  )
  ```

  - As a more didactic example, let us imagine while checking the loop invariant
  in the pseudocode below:
  ```
  while i < 5
    invariant i < 5
  do
    i := i + 1
  done
  ```
  we got the SMT-LIB file `INPUT.smt2`:
  ```
  (set-logic ALL)
  (declare-const i Int)
  (assert (and (< i 5) (not (< (+ i 1) 5))))
  (check-sat)
  (get-model)
  ```
  Execute the command
  ```sh
  alt-ergo --produce-models INPUT.smt2
  ```
  We got the output
  ```
  ; File "INPUT.smt2", line 4, characters 1-12: I don't know (0.6689) (2 steps) (goal g_1)

  unknown
  (
    (define-fun i () Int 4)
  )
  ```
  Alt-Ergo tells us that the `(check-sat)` could succeed with `i = 4`. Indeed,
  the loop invariant isn't preserved during the last iteration of the loop and
  the context is satisfiable. Let's fix our specification as follows:
  ```
  while i < 5
      invariant 0 <= i <= 5
  do
      i := i + 1
  end
  ```
  and fix our SMT-LIB input accordingly:
  ```
  (set-logic ALL)
  (declare-const i Int)
  (assert (and (< i 5) (not (<= (+ i 1) 5))))
  (check-sat)
  (get-model)
  ```
  Running the very same command, we got the expected output:
  ```
  ; File "INPUT.smt2", line 4, characters 1-12: Valid (0.5347) (1 steps) (goal g_1)

  unsat
  (error "No model produced.")
  ```
  Our invariant is valid!

### Output
The results of an Alt-ergo's execution have the following form :
```
File "<path_to_file>/<filename>", line <l>, characters <n-m>: <status> (<time in seconde>) (<number of steps> steps) (goal <name of the goal>)
```
The status can be `Valid`, `Invalid` or `I don't know`. If the input file is in
the SMT-LIB 2 format the status will be either `unsat`, `sat`, `unknown`.
You can force the status to be print in the SMT-LIB 2 form with the option `--output smtlib2`.

```{admonition} Note
When Alt-Ergo tries to prove a `goal` (with the native input language), it
actually tries to prove the unsatisfiability of its negation. That is
why you get `unsat` answer as an SMT-LIB 2 format output while proving a `Valid`
goal. The same goes for `Invalid` and `sat`.
```
