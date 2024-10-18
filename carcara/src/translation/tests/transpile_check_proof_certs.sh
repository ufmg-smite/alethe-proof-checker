#!/bin/bash

# Transpiles to Eunoia problem preludes and corresponding proof certificates,
# contained in $DIR. Uses $COMMAND to invoke 'carcara'.
DIR="./preludes/"
# TODO: installation-dependent relative paths
CARCARA_COMMAND="../../../../target/debug/carcara translate"
ETHOS_COMMAND="../../../../../ethos_fork/ethos/build/src/ethos"

# Loop through each file in the directory.
for FILE in "$DIR"/*; do
    # Check if it's a regular file
    if [ -f "$FILE" ]; then
        # Extract the file extension
        EXTENSION="${FILE##*.}"

        # Check if the file has the .smt2 extension
        if [ "$EXTENSION" == "smt2" ]; then
            # Proof certificate's name
            PROOF_CERTIFICATE="${FILE}_proof_certificate"

            EUNOIA_OUTPUT="${FILE}.eo"
            echo "----------------------"
            echo "About to process $FILE"

            # Use Carcara to transpile to Eunoia, redirect the output to 
            # "$EUNOIA_OUTPUT" 
            ${CARCARA_COMMAND} "$PROOF_CERTIFICATE" "$FILE" > "$EUNOIA_OUTPUT"

            # Check the return code of Carcara
            if [ $? -eq 0 ]; then
                ${ETHOS_COMMAND} "$EUNOIA_OUTPUT"
                if [ $? -eq 0 ]; then
                    # Print a success message
                    echo "Successfully processed $FILE and saved output to $EUNOIA_OUTPUT"
                    echo ""
                else
                    # rm "$EUNOIA_OUTPUT"
                    echo "Ethos failed on file $FILE"
                    echo ""
                fi
            else
                rm "$EUNOIA_OUTPUT"
                echo "Carcara failed on file $FILE"
                echo ""
            fi
        fi
    fi
done
