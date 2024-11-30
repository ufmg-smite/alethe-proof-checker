#!/bin/bash

# Generates Alethe proof certificates, using $COMMAND, from input problems
# contained in $DIR.
DIR="./problems/"
COMMAND="cvc5 --dump-proofs --proof-format-mode=alethe --proof-elim-subtypes"
CARCARA_COMMAND="../../../../target/release/carcara check --expand-let-bindings --allow-int-real-subtyping --ignore-unknown-rules"

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

            # Execute the command and redirect the output to the new file
            ${COMMAND} "$FILE" > "$PROOF_CERTIFICATE"

            # Check the return code of the command
            if [ $? -eq 0 ]; then
                ${CARCARA_COMMAND} "$PROOF_CERTIFICATE" "$FILE"

                if [ $? -eq 0 ]; then
                echo "Successfully processed $FILE and saved output to $PROOF_CERTIFICATE"
                echo ""
                else
                    # Print an error message
                    echo "Failed to process $FILE"
                    echo ""
                fi
            fi
        fi
    fi
done
