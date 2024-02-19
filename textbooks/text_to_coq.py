import sys
from openai import OpenAI
client = OpenAI()

def run_command(input_text):
    command = "Translate the following text to into literate Coq, keeping all text within comments and turning mathematical definitions, statements and theorems into valid Coq code: "
    completion = client.chat.completions.create(
        model="gpt-4-0125-preview",
        messages=[
        {"role": "system", "content": "You are an expert at the Coq proof assistant, capable of easily translating mathematical statements, theorems and proofs into the corresponding Coq code."},
        {"role": "user", "content": command + "\n" + input_text}
        ]
    )

    print(completion.choices[0].message.content.strip())


if __name__ == "__main__":
    if len(sys.argv) != 2:
        print("Usage: python script.py <input_file>")
        sys.exit(1)

    input_file = sys.argv[1]
    # output_file = sys.argv[2]

    # Read the content of the input file
    with open(input_file, 'r', encoding='utf-8') as file:
        input_text = file.read()

    # Run the command using the input text
    output_text = run_command(input_text)

    # Write the output to the output file
    # Not currently used
    # with open(output_file, 'w', encoding='utf-8') as file:
    #     file.write(output_text)
