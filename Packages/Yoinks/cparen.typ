#let iridis-palette = (
    color.rgb("#006400"),  // Dark Forest Green
    color.rgb("#8B0000"),  // Deep Crimson
    color.rgb("#000080"),  // Navy Blue
    color.rgb("#8B008B"),  // Dark Magenta
    color.rgb("#654321"),  // Dark Brown
    color.rgb("#004D4D"),  // Rich Teal
    color.rgb("#CC5500"),  // Burnt Orange
    color.rgb("#4B0082"),  // Indigo
    color.rgb("#800000"),  // Maroon
    color.rgb("#228B22"),  // Forest Green
)

#let need-regex-escape = (c) => {
	(c == "(") or (c == ")") or (c == "[") or (c == "]") or (c == "{") or (c == "}") or (c == "\\") or (c == ".") or (c == "*") or (c == "+") or (c == "?") or (c == "^") or (c == "$") or (c == "|") or (c == "-")
}

#let build-regex = (chars) => {
	chars.fold("", (acc, c) => {
		acc + (if need-regex-escape(c) { "\\" } else {""}) + c + "|"
	}).slice(0, -1)
}

#let copy-fields(equation, exclude:()) = {
	let fields = (:)
	for (k,f) in equation.fields() {
		if k not in exclude {
			fields.insert(k, f)
		}
	}
	fields
}

#let colorize-math(equation, i : 0) = {
		if type(equation) != content {
		return equation
	}
	if equation.func() == math.equation {
		// this is a hack to mark the equation as colored so that we don't colorize it again
		if equation.body.has("children") and equation.body.children.at(0) == [#sym.space.hair] {
			equation
		} else {
			math.equation([#sym.space.hair] + colorize-math(equation.body, i:i), block: equation.block)
		}
	} else if equation.func() == math.frac {
		math.frac(colorize-math(equation.num, i:i), colorize-math(equation.denom, i:i), ..copy-fields(equation, exclude:("num", "denom")))
	} else if equation.func() == math.accent {
			math.accent(colorize-math(equation.base, i:i), equation.accent, size: equation.size)
	} else if equation.func() == math.attach {
			math.attach(
				colorize-math(equation.base, i:i),
				..copy-fields(equation, exclude:("base",))
			)
	} else if equation.func() == math.cases {
		math.cases(..copy-fields(equation, exclude:("children")), ..equation.children.map(child => {
			colorize-math(child, i:i)
		}))
	} else if equation.func() == math.vec {context {
			let color = text.fill
			show: text.with(fill: iridis-palette.at(calc.rem(i, iridis-palette.len())))
			math.vec(
				..copy-fields(equation, exclude:("children")),
				..equation.children.map(child => {
					show: text.with(fill: color)
					colorize-math(child, i:i + 1)
				}),
			)		
		}} else if equation.func() == math.mat { context {
		let color = text.fill
		show: text.with(fill: iridis-palette.at(calc.rem(i, iridis-palette.len())))
		math.mat(
			..copy-fields(equation, exclude:("rows")),
			..equation.rows.map(row => row.map(cell => {
				show: text.with(fill: color)
				colorize-math(cell, i:i + 1)
			})),
		)
		show: text.with(fill: color)
	} } else if equation.has("body") {
		equation.func()(colorize-math(equation.body, i:i), ..copy-fields(equation, exclude:("body",)))
	} else if equation.has("children") { 
			let colorisation = equation.children.fold((i, ()), ((i, acc), child) => {
				if child == [(] {
					acc.push([
						#show: text.with(fill: iridis-palette.at(calc.rem(i, iridis-palette.len())))
						#equation.func()(([(],))])
					(i + 1, acc)
				} else if child == [)] {
					acc.push([
						#show: text.with(fill: iridis-palette.at(calc.rem(i - 1, iridis-palette.len())))
						#equation.func()(([)],))])
					(i - 1, acc)
				} else {
					acc.push(colorize-math(child, i:i))
					(i, acc)
				}
		})
		equation.func()(..copy-fields(equation, exclude:("children")), colorisation.at(1))
	} else if equation.has("child") { // styles
		equation.func()(colorize-math(equation.child, i:i), equation.styles)
	} else {
		equation
	}
}

#let colorize-code(counter, opening-parenthesis, closing-parenthesis, palette) = (body) =>  context {
	show regex(build-regex(opening-parenthesis)) :  body => context {
		show: text.with(fill: palette.at(calc.rem(counter.get(), palette.len()))) 
		body
		counter.update(n => n + 1)
	}

	show regex(build-regex(closing-parenthesis)) : body => context {
		counter.update(n => n - 1)
		text(fill: palette.at(calc.rem(counter.get() - 1, palette.len())), body)
	}
	body
}

#let iridis-show(
	opening-parenthesis: ("(","[","{"),
	closing-parenthesis: (")","]","}"),
	palette: iridis-palette,	
	body
) = {

	let counter = state("parenthesis", 0)
	

	show raw : colorize-code(counter, opening-parenthesis, closing-parenthesis, palette)
	show math.equation : colorize-math
 
	body
}
