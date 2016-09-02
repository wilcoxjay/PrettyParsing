# PrettyParsing

This is a simple library for implementing verified, human-readable, text-based representations
of data in Coq. 

## Build Instructions

PrettyParsing depends on [StructTact](https://github.com/uwplse/StructTact). This dependency is automatically detected by the `./configure` script if it is built in a sibling directory to this repository. Otherwise, you will need to edit `./configure` to set the `StructTact_PATH` environment variable to the path of your StructTact build.

```
./configure
make
```
