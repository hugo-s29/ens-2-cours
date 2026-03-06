import fitz

input_pdf = "input.pdf"
output_pdf = input("Save as file? ") + ".pdf"

doc = fitz.open(input_pdf)
out = fitz.open()

for page in doc:
    new_page = out.new_page(width=page.rect.width, height=page.rect.height)

    drawings = page.get_drawings()

    shape = new_page.new_shape()

    for d in drawings:
        rect = fitz.Rect(d["rect"])

        # Skip the page-sized white rectangle
        if (
            d["type"] == "f"
            and d["fill"] == (1.0, 1.0, 1.0)
            and rect == page.rect
        ):
            continue

        for item in d["items"]:
            op = item[0]

            if op == "re":
                shape.draw_rect(item[1])

            elif op == "l":
                shape.draw_line(item[1], item[2])

            elif op == "c":
                shape.draw_bezier(item[1], item[2], item[3], item[4])

        shape.finish(
            fill=d["fill"],
            color=d["color"],
            width=d["width"] if d["width"] else 0
        )

    shape.commit()

out.save(output_pdf)
