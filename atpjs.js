let uniquenessFilter = (v, i, a) => (a.indexOf(v) == i);
let knownFacts = []; //set of resolved propositions. {pred, args, result}

function betterTrim(text) {
	text = text.toString();
	let changes = true;
	while (changes) {
		changes = false;
		if (text.startsWith("(") && text.endsWith(")")) {text = text.substr(1, text.length - 2); changes = true;}
		text = text.trim();
	}
	return text;
}

//the primitive objects that predicates/relations act on
class Figure {
	constructor(l) {
		this.label = l;
		allFigures.push(this);
	}
	toString() {
		return this.label;
	}
	copy() {
		return new Variable(this.label);
	}
}

class QuantifiedVariable { //this is the forall x expressions
	constructor(l) {
		this.label = l;
	}
	toString() {
		return "<i>"+this.label+"</i>";
	}
	copy() {
		return new QuantifiedVariable(this.label);
	}
}

//the predicates/relations P_n that exist in this setup
class Predicate {
	constructor(l) {
		this.label = l;
	}
	toString() {
		return this.label;
	}
	copy() {
		return new Variable(this.label);
	}
}

class Proposition { //abstract, do not instantiate
	constructor() {}
	toString() {return "Undefined proposition";}
	copy() {return new Proposition();}
	listOfQuantifiedVariables() {return [];}
	performSubstitution(figure) {
		//find a QuantifiedVariable to choose for replacement with this figure
		let choices = this.listOfQuantifiedVariables();
		return choices.length ? this.substitute(choices[0], figure) : this;
	}
	substitute(quantifiedVariable, figure) {console.log("Wrong .substitute called. sorry"); return this;} //recursively used to perform substitutions. NEEDS TO MAKE COPY FOR YOU
	simplified() {return this;} //simplifies and returns this predicate simplified. needs to be ran several times until no more changes made (How to deliver that info?)
	submitKnowledge(state = true) {return;} //ONLY SHOULD BE PERFORMED BY THE HEAD PROPOSITION. recursively calls down. no need to report back up top though
}

class FalseProposition extends Proposition {
	constructor() {super();}
	toString() {return "false";}
	copy() {return this;}
	listOfQuantifiedVariables() {return [];}
	substitute(quantifiedVariable, figure) {return this;}
	simplified() {return this;}
	submitKnowledge(state = true) {if (state) console.log("Contradiction!!!");}
}

class TrueProposition extends Proposition {
	constructor() {super();}
	toString() {return "true";}
	copy() {return this;}
	listOfQuantifiedVariables() {return [];}
	substitute(quantifiedVariable, figure) {return this;}
	simplified() {return this;}
	submitKnowledge(state = true) {if (!state) console.log("Contradiction!!!");}
}

class NegationProposition extends Proposition {
	constructor(x) {
		super();
		this.inner = x;
	}
	toString() {
		return "(" + this.inner.toString() + ") is false";
	}
	copy() {
		return new NegationProposition(this.inner);
	}
	listOfQuantifiedVariables() {
		return this.inner.listOfQuantifiedVariables();
	}
	substitute(quantifiedVariable, figure) {
		return new NegationProposition(this.inner.substitute(quantifiedVariable, figure));
	}
	simplified() {
		if (this.inner instanceof TrueProposition) return new FalseProposition();
		if (this.inner instanceof FalseProposition) return new TrueProposition();
		if (this.inner instanceof NegationProposition) return this.inner.inner.copy();
		return this;
	}
	submitKnowledge(state = true) {
		this.inner.submitKnowledge(!state);
	}
}

class Predication extends Proposition {
	constructor(p, a) {
		super();
		this.pred = p;
		this.args = a; //is a list of Figures or Variables
	}
	toString() {
		let text = this.pred.toString();
		for (let i = 0; i < this.args.length; i++) text = text.replaceAll("${"+i+"}", this.args[i].toString());
		return text;
	}
	copy() {
		return new Predication(this.pred, this.args.concat());
	}
	listOfQuantifiedVariables() {
		return this.args.filter(x => x instanceof QuantifiedVariable);
	}
	substitute(quantifiedVariable, figure) {
		let c = this.copy();
		for (let i = 0; i < c.args.length; i++) if (c.args[i] == quantifiedVariable) c.args[i] = figure;
		return c;
	}
	simplified() {
		for (let arg of this.args) if (arg instanceof QuantifiedVariable) return this;
		for (let knownFact of knownFacts) {
			if (knownFact.pred != this.pred) continue;
			if (knownFact.args.length != this.args.length) continue;
			let argsMatch = true;
			for (let i = 0; i < knownFact.args.length; i++) if (knownFact.args[i] != this.args[i]) argsMatch = false;
			if (!argsMatch) continue;
			citationsUsedForPredications.push(knownFact.citation);
			return knownFact.result ? new TrueProposition() : new FalseProposition();
		}
		return this;
	}
	submitKnowledge(state = true) {
		knownFacts.push(new KnownFact(this.pred, this.args, state, this.citation));
	}
}

class AndProposition extends Proposition {
	constructor(a) {
		super();
		this.components = a;
	}
	toString() {
		return "( " + this.components.join(" and ") + " )";
	}
	copy() {
		return new AndProposition(this.components.concat());
	}
	listOfQuantifiedVariables() {
		let list = [];
		for (let component of this.components) list = list.concat(component.listOfQuantifiedVariables());
		return list.filter(uniquenessFilter);
	}
	substitute(quantifiedVariable, figure) {
		return new AndProposition(this.components.map(x => x.substitute(quantifiedVariable, figure)));
	}
	simplified() {
		let c = this.copy();
		c.components = c.components.map(x => x.simplified());
		for (let component of c.components) if (component instanceof FalseProposition) return new FalseProposition();
		c.components = c.components.filter(x => !(x instanceof TrueProposition));
		if (c.components.length == 1) return c.components[0];
		return c;
	}
	submitKnowledge(state = true) {
		if (state) for (let component of this.components) component.submitKnowledge(state);
	}
}

class OrProposition extends Proposition {
	constructor(a) {
		super();
		this.components = a;
	}
	toString() {
		return "( " + this.components.join(" or ") + " )";
	}
	copy() {
		return new OrProposition(this.components.concat());
	}
	listOfQuantifiedVariables() {
		let list = [];
		for (let component of this.components) list = list.concat(component.listOfQuantifiedVariables());
		return list.filter(uniquenessFilter);
	}
	substitute(quantifiedVariable, figure) {
		return new OrProposition(this.components.map(x => x.substitute(quantifiedVariable, figure)));
	}
	simplified() {
		let c = this.copy();
		c.components = c.components.map(x => x.simplified());
		for (let component of c.components) if (component instanceof TrueProposition) return new TrueProposition();
		c.components = c.components.filter(x => !(x instanceof FalseProposition));
		if (c.components.length == 1) return c.components[0];
		return c;
	}
	submitKnowledge(state = true) {
		if (!state) for (let component of this.components) component.submitKnowledge(state); //demorgans law. in disguise
	}
}

class LogicalEquivalenceProposition extends Proposition {
	constructor(a) {
		super();
		this.components = a;
	}
	toString() {
		return "( " + this.components.join(" ⟺ ") + " )";
	}
	copy() {
		return new LogicalEquivalenceProposition(this.components.concat());
	}
	listOfQuantifiedVariables() {
		let list = [];
		for (let component of this.components) list = list.concat(component.listOfQuantifiedVariables());
		return list.filter(uniquenessFilter);
	}
	substitute(quantifiedVariable, figure) {
		return new LogicalEquivalenceProposition(this.components.map(x => x.substitute(quantifiedVariable, figure)));
	}
	simplified() {
		let c = this.copy();
		for (let component of c.components) if (component instanceof TrueProposition) {
			let components = this.components.filter(x => !(x instanceof TrueProposition));
			if (components.length == 1) return components[0];
			if (components.length > 1) return new AndProposition(components);
		}
		for (let component of c.components) if (component instanceof FalseProposition) {
			let components = this.components.filter(x => !(x instanceof FalseProposition));
			components = components.map(x => new NegationProposition(x));
			if (components.length == 1) return components[0];
			if (components.length > 1) return new AndProposition(components);
		}
		c.components = c.components.map(x => x.simplified());
		//for (let component of c.components) if (component instanceof TrueProposition) return new AndProposition(this.components.filter(x => !(x instanceof TrueProposition)));
		//for (let component of c.components) if (component instanceof FalseProposition) return new AndProposition(this.components.filter(x => !(x instanceof FalseProposition)).map(x => new NegationProposition(x)));
		if (c.components.length == 1) return c.components[0];
		return c;
	}
}

class ImplicationProposition extends Proposition {
	constructor(p, q) {
		super();
		this.hypothesis = p;
		this.consequence = q;
	}
	toString() {
		return "( " + this.hypothesis.toString() + " → " + this.consequence.toString() + " )";
	}
	copy() {
		return new ImplicationProposition(this.hypothesis.copy(), this.consequence.copy());
	}
	listOfQuantifiedVariables() {
		return this.hypothesis.listOfQuantifiedVariables().concat(this.consequence.listOfQuantifiedVariables()).filter(uniquenessFilter);
	}
	substitute(quantifiedVariable, figure) {
		return new ImplicationProposition(this.hypothesis.substitute(quantifiedVariable, figure), this.consequence.substitute(quantifiedVariable, figure));
	}
	simplified() {
		if (this.hypothesis instanceof TrueProposition) return this.consequence;
		if (this.consequence instanceof FalseProposition) return new NegationProposition(this.hypothesis);
		if (this.consequence instanceof NegationProposition && this.hypothesis instanceof NegationProposition) return new ImplicationProposition(this.consequence.inner, this.hypothesis.inner);
		return new ImplicationProposition(this.hypothesis.simplified(), this.consequence.simplified());
	}
}

class KnownFact { //predications that have been resolved
	constructor(p, a, r, c) {
		this.pred = p;
		this.args = a;
		this.result = r;
		this.citation = c; //the theorem # we got this fact from
	}
}

let citationsUsedForPredications = []; //global variable to track which citations were invoked when simplifying a theorem using known predications. reset to [] before .simplified(), accessed when reporting citations
function tryReadKnowledge(predication) { //reads a proposition. if it's a predication, looks for it in known facts and gives u back simpler (boolean) form. ALL ARGS MUST BE FIGURES, no qtfied vars
	if (!(predication instanceof Predication)) return predication;
	for (let arg of predication.args) if (arg instanceof QuantifiedVariable) return predication;
	for (let knownFact of knownFacts) {
		if (knownFact.pred != predication.pred) continue;
		if (knownFact.args.length != predication.args.length) continue;
		for (let i = 0; i < knownFact.args.length; i++) if (knownFact.args[i] != predication.args[i]) continue;
		return knownFact.result ? new TrueProposition() : new FalseProposition();
	}
	return predication;
}

let table = document.querySelector("table");
function registerProposition(proposition, label) { //assumes this proposition is (directly) stored in theorems
	//check if this isn't a clearly redundant proposition
	let propositionText = betterTrim(proposition.toString());
	if (propositionText == "true") return;
	for (let t of theorems) if (betterTrim(t.toString()) == propositionText) return; //redundant
	proposition.citation = theorems.length;
	theorems.push(proposition);
	let tr = table.appendChild(document.createElement("tr"));
	let td = [];
	for (let i = 0; i < 4; i++) {
		td.push(tr.appendChild(document.createElement("td")));
		td[i].setAttribute("class", ["number", "label", "formula", "actions"][i]);
	}
	td[0].innerHTML = "("+(1+proposition.citation)+")";
	td[1].innerHTML = label;
	td[2].innerHTML = propositionText;
	let buttonDemands = [];
	if (proposition.simplified().toString() != proposition.toString() || true) buttonDemands.push(["Simplify", function() {
		uiSimplification(proposition);
	}]);
	if (proposition.listOfQuantifiedVariables().length) buttonDemands.push(["Substitute", function() {
		if (document.querySelector(".modal")) for (let e of document.querySelectorAll(".modal")) removeModal(e);
		let modal = document.body.appendChild(document.createElement("div"));
		modal.setAttribute("class", "modal");
		let ogTheorem = modal.appendChild(document.createElement("p"));
		ogTheorem.innerHTML = betterTrim(proposition.toString());
		let cancel = modal.appendChild(document.createElement("button"));
		cancel.setAttribute("class", "cancel");
		cancel.innerText = "X";
		cancel.onclick = function() {
			removeModal(modal);
		}
		let qtList = proposition.listOfQuantifiedVariables();
		for (let qt of qtList) {
			let div = modal.appendChild(document.createElement("div"));
			let label = div.appendChild(document.createElement("label"));
			label.innerHTML = "Substitute " + qt.toString() + " to ";
			let select = div.appendChild(document.createElement("select"));
			for (let fig of allFigures) {
				let option = select.appendChild(document.createElement("option"));
				option.innerHTML = fig.toString();
				option.value = allFigures.indexOf(fig);
				//if qt# mod fig length is this fig, this fig is active
				if (qtList.indexOf(qt) % allFigures.length == option.value) select.value = option.value;
			}
			select.onchange = updateSubmitButtonText;
		}
		let submit = modal.appendChild(document.createElement("button"));
		submit.setAttribute("class", "submit");
		updateSubmitButtonText();
		submit.onclick = function() {
			//get list of figures that were chosen
			let figs = [];
			for (let select of modal.querySelectorAll("select")) figs.push(allFigures[select.value]);
			uiSubstitution(proposition, qtList, figs);
			removeModal(modal);
		}
		function updateSubmitButtonText() {
			let figs = [];
			for (let select of modal.querySelectorAll("select")) figs.push(allFigures[select.value]);
			let newProposition = proposition;
			for (let i = 0; i < figs.length; i++) newProposition = newProposition.substitute(qtList[i], figs[i]);
			submit.innerHTML = betterTrim(newProposition.toString());
		}
	}]);
	for (let [text, funct] of buttonDemands) {
		let button = td[3].appendChild(document.createElement("button"));
		button.innerHTML = text;
		button.onclick = funct;
	}
	proposition.submitKnowledge();
	checkSimplifiability();
	for (let successPossibility of successLooksLike) if (propositionText == successPossibility) finished();
}

let theorems = [];
let allFigures = [];

function uiSubstitution(theorem, qtList, figureList) {
	if (fini) return;
	if (!theorem) return;
	if (!qtList.length || !figureList.length || (qtList.length != figureList.length)) return;
	let variableChoice = theorem.listOfQuantifiedVariables()[0];
	if (!variableChoice) return;
	let newTheorem = theorem;
	for (let i = 0; i < qtList.length; i++) newTheorem = newTheorem.substitute(qtList[i], figureList[i]);
	registerProposition(newTheorem, "from (" + (1+theorem.citation)+"), sub. " + qtList.join(", ") + " to " + figureList.join(", "));
}

function uiSimplification(theorem) {
	if (fini) return;
	if (!theorem) return;
	citationsUsedForPredications = [];
	let newTheorem = theorem.simplified();
	if (newTheorem.toString() == theorem.toString()) return;
	let text = "simplified (" + (1+theorem.citation)+")";
	citationsUsedForPredications = citationsUsedForPredications.filter(x => x >= 0);
	if (citationsUsedForPredications.length) text += ", using " + citationsUsedForPredications.map(x => "("+(1+x)+")").join(", ");
	registerProposition(newTheorem, text);
}

//the fancy css out
function removeModal(modal) {
	modal.style.animation = "0.2s modal-exit";
	setTimeout(function() {modal.remove();}, 200);
}

//updates all the theorems shown on screen for their lil "Simplify" buttons
//simplify buttons are hidden when, as of right now, they would just simplify to identical expression (or just "true")
function checkSimplifiability() {
	let simplifyButtons = Array.from(document.querySelectorAll(".actions button")).filter(x => x.innerText == "Simplify");
	for (let i = 0; i < theorems.length; i++) {
		let attemptedSimplification = theorems[i].simplified();
		let alreadySimple = betterTrim(attemptedSimplification.toString()) == betterTrim(theorems[i].toString()) || attemptedSimplification instanceof TrueProposition;
		//simplifyButtons[i].style.display = alreadySimple ? "none" : "block";
		simplifyButtons[i].style.display = alreadySimple ? "none" : "block";
	}
}

let problemStatementHTML = "";
let successLooksLike = [];

function initialize() {
	document.querySelector("#problem-statement").innerHTML = problemStatementHTML;
	for (let tr of table.querySelectorAll("tr")) tr.setAttribute("class", "given");
}

let fini = false;
function finished() {
	fini = true;
	for (let e of document.querySelectorAll(".actions button")) e.setAttribute("disabled", "true");
	document.querySelector("tr:last-child .actions").innerHTML = "";
	let finishedMark = document.querySelector("tr:last-child .actions").appendChild(document.createElement("span"));
	finishedMark.setAttribute("class", "finished-mark");
	finishedMark.innerText = "✓";
	let finishedMark2 = document.querySelector("tr:last-child .actions").appendChild(document.createElement("span"));
	finishedMark2.setAttribute("class", "finished-mark-2");
	finishedMark2.innerText = "Done";
}