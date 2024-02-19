import fitz  # PyMuPDF
import sys

def extract_text_with_math(pdf_path, output_path):
    # Open the PDF file
    pdf_document = fitz.open(pdf_path)
    
    # Initialize an empty string to store the text
    text = ""
    
    # Iterate over all pages in the PDF
    for page_num in range(pdf_document.page_count):
        # Get the page
        page = pdf_document.load_page(page_num)
        
        # Extract text with inline math
        text += page.get_text("text") + "\n"
        
        # Extract text within math blocks (if available)
        blocks = page.get_text("dict")["blocks"]
        for block in blocks:
            if block.get("type") == 1:  # Block containing math
                if "lines" in block:
                    for line in block["lines"]:
                        for span in line["spans"]:
                            if span["text"] != "":
                                text += f"\\({span['text']}\\)"  # Enclose math in LaTeX $$
                        text += "\n"
                elif "text" in block:
                    text += f"\\({block['text']}\\)\n"  # Enclose math in LaTeX $$
    
    # Close the PDF file
    pdf_document.close()
    
    # Write the extracted text to the output file
    with open(output_path, 'w', encoding='utf-8') as txt_file:
        txt_file.write(text)

if __name__ == "__main__":
    if len(sys.argv) != 3:
        print("Usage: python script.py <input_pdf> <output_txt>")
        sys.exit(1)
    
    input_pdf = sys.argv[1]
    output_txt = sys.argv[2]
    
    # Convert the PDF to text with LaTeX-formatted math
    extract_text_with_math(input_pdf, output_txt)
