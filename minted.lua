function CodeBlock(el)
  local lang = el.classes[1]

  local opts = ""
  function sep()
    if #opts == 0 then
      return ""
    else
      return ", "
    end
  end
  for key, value in pairs(el.classes) do
    if key ~= 1 then
      opts = opts .. sep() .. value
    end
  end
  for key, value in pairs(el.attributes) do
    opts = opts .. sep() .. key ..'=' .. value
  end

  return pandoc.RawBlock("latex",
    "\\begin{minted}[" .. opts .. "]{" .. lang .. "}\n" ..
      el.text ..
    "\n\\end{minted}"
  )
end
