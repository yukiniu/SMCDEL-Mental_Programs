#!/bin/bash

output_file="generator.hs"

# Write header of the output file
cat <<EOL > "$output_file"
module Main where

import SMCDEL.Internal.TexDisplay

EOL

# Extract unique module imports from list.txt and add to output file
awk -F'[:]' '{sub(/src\//, "", $1); sub(/\.(hs$|lhs)$/, "", $1); gsub("/", ".", $1); print "import " $1}' list.txt  | sort -uu >> "$output_file"

# Write the main function header
cat <<EOL >> "$output_file"

main :: IO ()
main = do
EOL

# Process each line in list.txt to generate `makeSvg` calls
while IFS= read -r line; do
    # Extract module path and function name
    module_path=$(echo "$line" | awk -F'[:]' '{sub(/src\//, "", $1); sub(/\.(hs$|lhs)$/, "", $1); gsub("/", ".", $1); print $1}')
    func_name=$(echo "$line" | sed -n "s/.*'\\([^']*\\)).*/\\1/p")

    # Add refreshSvg line to output file
    echo "  refreshSvg \"$func_name\"" $module_path.$func_name >> "$output_file"
done < "list.txt"

echo "Finished making $output_file."
