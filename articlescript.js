//tiny script file to automatically do things to every article

//set inline delimeters for mathjax
MathJax = {
	tex: {
		inlineMath: [['$', '$']]
	}
};

//css
add_head_link("stylesheet", "../articlestyle.css");

//load font
add_head_link("preconnect", "https://rsms.me/");
add_head_link("stylesheet", "https://rsms.me/inter/inter.css");

//helper functions
function add_script(url) {
	let script = document.body.appendChild(document.createElement("script"));
	script.setAttribute("async", "");
	script.setAttribute("src", url);
}

function add_head_link(rel, href) {
	let link = document.head.appendChild(document.createElement("link"));
	link.setAttribute("rel", rel);
	link.setAttribute("href", href);
}

//load mathjax
add_script("https://cdn.jsdelivr.net/npm/mathjax@3/es5/tex-chtml.js");

let nav = document.body.appendChild(document.createElement("nav"));
nav.setAttribute("id", "toc");
for (let h2 of document.querySelectorAll("h2")) {
	let a = nav.appendChild(document.createElement("a"));
	a.innerText = h2.innerText;
	a.setAttribute("href", "#"+h2.getAttribute("id"));
}

let otherart = nav.appendChild(document.createElement("div"));
otherart.innerText = "Read the other post:";
let otherartA = otherart.appendChild(document.createElement("a"));
otherart.setAttribute("class", "other-article");
if (document.querySelector("title").innerText.startsWith("W")) {
	//we are in motivation article
	otherartA.setAttribute("href", "../building");
	otherartA.innerText = "My experience building an ATP-like program";
} else {
	//we are in building article
	otherartA.setAttribute("href", "../motivation");
	otherartA.innerText = "We already know how to prove the twin prime conjecture: A motivation for trying to build an ATP-like program";
}