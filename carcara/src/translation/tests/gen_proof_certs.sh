#!/bin/bash

# Generates Alethe proof certificates, using $COMMAND, from problem preludes 
# contained in $DIR.
DIR="./preludes/"
COMMAND="cvc5 --dump-proofs --proof-format-mode=alethe"

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
                # Print a success message
                echo "Successfully processed $FILE and saved output to $PROOF_CERTIFICATE"
                echo ""
            else
                rm "$PROOF_CERTIFICATE"
                # Print an error message
                echo "Failed to process $FILE"
                echo ""
            fi
        fi
    fi
done
