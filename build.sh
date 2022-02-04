#!/bin/bash

DIR="$(dirname "$0")"
cd "$DIR"

# rm -rf build

# This is a horrible hack, but I could not find a way to just build a file.
# Trying to execute some function, even if it does not exists, does have the side effect of building
# the module, and caching it for future dependency resolving

idris2 -x Main Lib/PCF/Types.tex        >/dev/null  
idris2 -x Main Lib/PCF/Terms.tex        >/dev/null  
idris2 -x Main Lib/PCF/TypeOf.tex       >/dev/null  
idris2 -x Main Lib/PCF/Substitute.tex   >/dev/null 
idris2 -x Main Lib/PCF/Reduction.tex    >/dev/null 
idris2 -x Main Lib/TypedTerms.tex       >/dev/null 

echo "Done"
