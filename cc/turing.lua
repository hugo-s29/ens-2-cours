function draw_tape(t, y, cell_size, braces)
  local x = (t.x_start ~= nil) and t.x_start or 3
  local cell_w = t.cell_w or cell_size or 0.45
  local cell_h = t.cell_h or cell_size or 0.45
  local head_pos = t.head_pos or 1
  local content_fmt = t.content_fmt or "raw" -- "raw" | "texttt"

  tex.print(string.format("\\filldraw (%f,%f) rectangle ++(0.15,%f);", x, y, cell_h))
  x = x + 0.15

  for i = 1, t.n do
    tex.print(string.format("\\draw (%f,%f) rectangle ++(%f,%f);", x, y, cell_w, cell_h))

    local content = ""
    if type(t.content) == "table" then
      content = t.content[i] or ""
    elseif i == 1 and type(t.content) == "string" then
      content = t.content
    end

    if content ~= "" then
      local node_text = content
      if content_fmt == "texttt" then
        node_text = "\\texttt{" .. content .. "}"
      end
      tex.print(string.format("\\node at (%f,%f) {%s};", x + cell_w/2, y + cell_h/2, node_text))
    end

    x = x + cell_w
  end

  tex.print(string.format("\\draw[very thick, white] (%f,%f) -- (%f,%f);", x, y, x, y + cell_h))
  tex.print(string.format("\\draw[decorate,decoration={zigzag,segment length=3pt,amplitude=1pt}] (%f,%f) -- (%f,%f);", x, y, x, y + cell_h))

  if t.label ~= nil and t.label ~= "" then
    tex.print(string.format("\\node[right=4mm] at (%f,%f) {%s};", x, y + cell_h/2, t.label))
  end

  braces = braces or {}
  for _, brace in ipairs(braces) do
    local x_start = ((t.x_start ~= nil) and (t.x_start + 0.15) or 3.15) + brace.from * cell_w
    local x_end = ((t.x_start ~= nil) and (t.x_start + 0.15) or 3.15) + (1 + brace.to) * cell_w
    local y_gap = cell_h / 5
    tex.print(string.format(
      "\\draw[decorate,decoration=calligraphic brace, thick] (%f, %f) to node[below] {%s} (%f, %f);",
      x_end, y - y_gap, brace.text, x_start, y - y_gap
    ))
  end

  return ((t.x_start ~= nil) and (t.x_start + 0.15) or (3 + 0.15)) + (head_pos - 1) * cell_w + cell_w/2
end

function turing_diagram(name, tapes)
  local y = 0
  local dy = -0.9
  tex.print("\\node[draw,minimum size=8mm] (M) at (0,0) {$" .. name .. "$};")
  for i, t in ipairs(tapes) do
    local head_x = draw_tape(t, y)
    local above_y = y + 0.45 + 0.3
    tex.print(string.format("\\draw[->] (M.east) -- ++(0.8,0) -- (1.2,%f) -- (%f,%f) -- (%f,%f);", 
      above_y, head_x, above_y, head_x, y + 0.45))
    y = y + dy
  end
end

function draw_spacetime_diagram(config)
  local cell_w = config.cell_w or 0.45
  local cell_h = config.cell_h or 0.45
  local row_gap = config.row_gap or 0.3
  local x_start = config.x_start or 2
  local y_start = config.y_start or 0
  local tape_width = config.tape_width or 7

  for t, step in ipairs(config.steps) do
    local y = y_start + (t - 1) * (cell_h + row_gap)

    local head_x = draw_tape({
      x_start = x_start,
      cell_w = cell_w,
      cell_h = cell_h,
      n = tape_width,
      head_pos = step.head_pos or 1,
      content = step.content,
      label = "", -- spacetime has its own left-side step label
      content_fmt = "texttt",
    }, y)

    local above_y = y + cell_h + 0.15
    tex.print(string.format("\\draw[->] (%f,%f) -- (%f,%f);", head_x, above_y, head_x, y + cell_h))

    tex.print(string.format("\\node[left] at (%f,%f) {$%d$};", x_start - 0.3, y + cell_h/2, t - 1))
  end

  local y_top = y_start + (#config.steps - 1) * (cell_h + row_gap)
  local x_end = x_start + 0.15 + tape_width * cell_w
  local axis_origin_x = x_start - 0.3
  local axis_origin_y = y_start - 0.3

  tex.print(string.format("\\draw[->] (%f,%f) -- (%f,%f) node[left] {$t$};",
    axis_origin_x, axis_origin_y, axis_origin_x, y_top + cell_h + 0.5))

  tex.print(string.format("\\draw[->] (%f,%f) -- (%f,%f) node[below] {$i$};",
    axis_origin_x, axis_origin_y, x_end + 0.5, axis_origin_y))
end

spacer = "\\texttt{\\#}"
dots = "$\\cdots$"

