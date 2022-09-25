# 0.3.0 (2022-09-24)

* Change integral literals to express a preferred base.
* Change floating-point literals to be pre-converted to digits.
* Add a representation of infinite and NaN values.
* Add several utility functions for formatting int and float literals.
* Add configuration of the Generic functionality to suppress record syntax.
* Don't use strict fields for the spine of the `Portrayal` tree structure.

# 0.2.0 (2021-09-17)

* Split Atom into literals, identifiers, and opaque text.
* Make operator names and record field names `Ident`s.
* Special-case `String`s so they don't get formatted as lists of `Char`s.

# 0.1.1 (2021-09-17)

Transitional version towards 0.2.0.

* Add `Name` and `Opaque` pattern synonyms.

# 0.1.0.0 (2021-09-02)

Initial version.
