# 0.2.1

* Split into `Data.Portray.Portrayal` and `Data.Portray.Class` modules.
* Keep a backwards-compatible (and convenient) `Data.Portray` reexport module.
* Add a lot of instances from `base`, `containers`, `text`, and `bytestring`.

# 0.2.0

* Split Atom into literals, identifiers, and opaque text.
* Make operator names and record field names `Ident`s.
* Special-case `String`s so they don't get formatted as lists of `Char`s.

# 0.1.1

Transitional version towards 0.2.0.

* Add `Name` and `Opaque` pattern synonyms.

# 0.1.0.0

Initial version.
