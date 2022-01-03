# Generate the OCaml files to Coq using `coq-of-ocaml`

if ARGV.size < 3 then
  puts "Usage:"
  puts "  ruby generate.rb easier_proofs_path examples_path target_path"
  exit(1)
end

easier_proofs_path, examples_path, target_path = ARGV
full_path = File.join(easier_proofs_path, examples_path, target_path)

# Generate

generate_files =
  Dir.glob(File.join(full_path, "*.ml")) 
for ocaml_file_name in generate_files.sort do
    command = "cd #{full_path} && coq-of-ocaml #{File.basename(ocaml_file_name)}"
  system(command)
end
