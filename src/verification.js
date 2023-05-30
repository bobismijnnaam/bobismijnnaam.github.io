/*
    Snap! code static verification.
*/

// TODO:
//   Non supported:
//     * up vars


var _ = undefined;

modules.verification = '2020-08-01';

var BoogieNode;
BoogieNode.prototype = {};
BoogieNode.prototype.constructor = BoogieNode;
BoogieNode.counter = -1;

function NewId () {
    BoogieNode.counter += 1;
    return BoogieNode.counter;
}

function BoogieNode(block, error, mssg){
    this.init(block, error, mssg);
}

String.prototype.compile = function () {
    return this;
}

BoogieNode.prototype.init = function(
    block = null, 
    error = false, 
    mssg = ""
){
    // this.globals = {};
    this.boogieString = "";
    this.errorMessage = mssg;
    this.error = error;
    this.block = block;
    this.ignore = false;
}

BoogieNode.prototype.toString = function () {
    return 'a ' +
        (this.constructor.name ||
            this.constructor.toString().split(' ')[1].split('(')[0]) +
        ' ';
};

BoogieNode.prototype.compile = function () {
    console.warn("Unimplemented compile method for", 
        this.constructor.name);
    return "";
}

BoogieNode.prototype.inferTypes = function ( expect ) {
    console.warn(
        "Unimplemented inferTypes method for", this.constructor.name);
    return;
}

//-------------------------------------------------------------------------
var BoogieProcedure;
BoogieProcedure.typeMap = {};      // string -> {int, int, bool, null}

BoogieProcedure.set_type = function (name, type) {
    let t = BoogieProcedure.typeMap[name];
    if (t != type && t != null) {
        console.error(
            `${name} already had type ${t}. Overriding with ${type}`);
    }
    BoogieProcedure.typeMap[name] = type;
}

BoogieProcedure.get_type = function (name, dropBack=true) {
    let result = null;
    if (typeof name === "string") {
        if (isNaN(name)) {
            result = BoogieProcedure.typeMap[name];
            if (result == undefined && dropBack){
                console.warn(
                    `Undefined type for ${name}. Returning int instead.`);
                result = 'int';
            } 
        }else{
            result = 'int';
        }
    } else {
        // name is BoogieExpression or something is wrong. 
        result = name.inferTypes(undefined);
    }
    return result;
}

BoogieProcedure.prototype = new BoogieNode();
BoogieProcedure.prototype.constructor = BoogieProcedure;
BoogieProcedure.uber = BoogieNode.prototype;

function BoogieProcedure (block=null, error=false, mssg="") {
    BoogieProcedure.uber.init.call(this, block, error, mssg);
    this.init();
}

BoogieProcedure.prototype.init = function () {
    this.contextVarDecls = [];
    this.contextAxioms = [];
    this.localVarDecls = [];
    this.localInitializations = [];
    this.name = "";
    this.inputs = null;
    this.requires = [];     // specifications
    this.ensures = [];      // specifications
    this.results = [];
    this.modifies = [];
    this.body = [];         // list of commands
    this.reports = false;
}

BoogieProcedure.prototype.compile = function () {

    this.passInferTypes();
    this.passVisitLists();
    this.passMoveVarDeclToTop();

    // then build the Boogie string
    this.boogieString += "// This Boogie code has been compiled from"
        + " a verifiable Snap! project.\n\n";

    for (i of this.inputs.filter(i => !i.ignore)) {
        this.boogieString += `var ${i.compile()};\n`;
        this.modifies.push(i.label.compile());
    }    

    for (x of this.contextVarDecls) this.boogieString += `${x}\n`;
    for (x of this.contextAxioms) this.boogieString += `${x}\n`;

    this.boogieString += "\n" + "procedure " + this.name.compile() + " ()";
    
    this.boogieString += " " + this.compileReturnType() + "\n";
    this.boogieString += `modifies ${compile_list_length('result')};\n`;
    for (x of this.modifies) {
        this.boogieString += "modifies " + x + ";\n";
    }
    for (x of this.requires) {
        this.boogieString += "requires " + x.compile() + ";\n";
    }
    for (x of this.ensures) {
        this.boogieString += "ensures " + x.compile() + ";\n";
    }

    this.boogieString += "{\n";

    for (x of this.localVarDecls) {
        this.boogieString += x+"\n";
    }

    for (x of this.localInitializations) {
        this.boogieString += x;
    }

    for (x of this.body) {
        this.boogieString += x.compile();
        this.boogieString += "\n";
    }
    this.boogieString += "}\n";

    return this.boogieString;
}

BoogieProcedure.prototype.passInferTypes = function () {
    // We can infer types from the body commands, and
    // from require and ensure specs.

    for (c of this.body) {
        c.inferTypes(null);
    }

    for (r of this.requires) {
        r.inferTypes('bool');
    }

    for (e of this.ensures) {
        e.inferTypes('bool');
    }
}

BoogieProcedure.prototype.passProcessReturns = function () {
}

BoogieProcedure.prototype.passVisitLists = function () {
    // Lists are translated to maps from integer to the
    // Snap list type. Since maps have infinite domain
    // we will need to define an upper bound for list 
    // (lower bound is 0).

    // for result if it happens to be a list
    this.contextVarDecls.push(
        `var ${compile_list_length('result')} : int;`);

    // For input move them to global scope so they can be modified,
    // define their length variable and add a modified clause to 
    // the function contract:

    for (x of this.inputs) {
        let name = x.label.compile();
        let type = BoogieProcedure.get_type(name);
        if (type.startsWith('list')) {
            // to global
            x.ignore = true;
            this.contextVarDecls.push(
                `var ${name} : ${type_to_boogie(type)};`);
            this.modifies.push(name);
            // the length
            let len =  compile_list_length(name);
            this.contextVarDecls.push(`var ${len} : int;`);
            this.requires.push(
                new BoogieLogicOp(
                    null, _, _, 2, ">=",
                    len,"0"));
            this.modifies.push(len);
            BoogieProcedure.set_type(len, 'int');
        }
    }

    // Turn inlined lists to explicit lists
    let lists = this.allChild(BoogieList);
    for (l of lists) {
        // l.ignore = true;
        let name = l.compile_name();
        let len  = l.compile_length();
        let t = type_to_boogie(BoogieProcedure.get_type(name));
        this.localVarDecls.push(`var ${name} : ${t};`);
        this.localVarDecls.push(`var ${len} : int;`);
        this.localInitializations.push(`${len} := 0;`);
    }

    let ranges = this.allChild(BoogieRange);

    for (r of ranges) {
        let name = r.compile_name();
        let len = r.compile_length();

        this.localVarDecls.push(`var ${name} : [int]int;`);
        this.localVarDecls.push(`var ${len} : int;`);
        this.localInitializations.push(`${len} := 0;`);
    }
}

function type_to_boogie (t) {
    result = "";
    if (t == null) {
        result = "null";
    } else if (t.startsWith("list")) {
        result += "[int]";
        t = t.split(' ');
        t.shift();
        let last = t.pop();
        for (x of t) {
            result += `[${x}]`;
        }
        result += last;
    }else{
        result = t;
    }
    return result;
}

function get_inner_type (t) {
    result = null;
    if (t != null && t.startsWith("list")) {
        result = t.split(' ');
        result.shift();
        result = result.join(' ');
    } 
    return result;
}

BoogieProcedure.prototype.passMoveVarDeclToTop = function () {

    let varDecl = this.allChild(BoogieVariableDeclaration);

    for (x of varDecl) {
        this.localVarDecls.push(x.compile());
        let i = varDecl.indexOf(x);
        x.ignore = true;
    }

}

BoogieNode.prototype.allChild = function (ctr=BoogieNode) {
    let res = [];

    let aux = [this];
    while (aux.length>0) {
        let x = aux.shift();
        if (x instanceof BoogieNode | x instanceof Array) {
            if (x instanceof ctr) {
                res.push(x);
                
            }
            for (y of Object.keys(x)) {
                if (x[y] instanceof Array) {
                    aux = aux.concat(x[y]);
                }else{
                    aux.push(x[y]);
                }
            }
        }
    }
    return res;
}

BoogieProcedure.prototype.compileReturnType = function () {
    var returns = [];
    for (x of this.body) {
        returns = returns.concat(x.allChild(BoogieReturn));
    }
    //  = this.body.filter(x => x instanceof BoogieReturn);
    retTypes = returns.map(x=>BoogieProcedure.get_type(x));
    if ((new Set(retTypes)).size > 1) {
        this.block.showBubble(
            "Warning: you need a single return type to run Boogie.");
    }
    let t = BoogieProcedure.get_type('result');
    return retTypes.length === 0 ? "" : 
        "returns (result: " + type_to_boogie(t) + ")";
}


//-------------------------------------------------------------------------
var BoogieExpression;

BoogieExpression.prototype = new BoogieNode();
BoogieExpression.prototype.constructor = BoogieExpression;
BoogieExpression.uber = BoogieNode.prototype;

function BoogieExpression (
    block=null, 
    error=false, 
    mssg="",
    arity=0,
    type=null,
    op=null,
    lhs=null, 
    rhs=null)
{
    this.init(block, error, mssg, arity, type, op, lhs, rhs);
}

BoogieExpression.prototype.init = function (
    block=null,
    error=false,
    mssg="",
    arity=0,
    type=null,
    op=null, 
    lhs=null, 
    rhs=null) 
{
    BoogieExpression.uber.init.call(this, block, error, mssg);
    this.arity = arity;
    this.type = type;
    this.op = op;
    this.lhs = lhs;
    this.rhs = rhs;
}

BoogieExpression.prototype.compile = function () {
    if (this.arity === 0) {
        this.boogieString = this.op.compile();
    }else if (this.arity === 1) {
        this.boogieString = 
            "(" + 
            this.op.compile() +
            "(" +
            this.lhs.compile() +
            "))";
    }else if (this.arity === 2) {
        console.log(this.lhs)
        let tl = BoogieProcedure.get_type(this.lhs);
        if (!tl.startsWith('list')) {
            this.boogieString = 
            "(" + 
            this.lhs.compile() + " " +
            this.snapToBoogieOperator(this.op.compile()) + " " +
            this.rhs.compile() +
            ")";
        }else{
            this.boogieString = this.compileListEq();
        }
    }else{
        // is this useful???
        this.boogieString = "{{Error compiling" + this + "}}"; 
    }
    return this.boogieString;
}

BoogieExpression.prototype.compileListEq = function () {
    "Returns Boogie code for comparing two lists."

    let lname = this.lhs.get_name();
    let rname = this.rhs.get_name();

    let ll = compile_list_length(lname);
    let rl = compile_list_length(rname);

    let idx = "idx" + NewId();

    this.boogieString = `(${ll} == ${rl}) && (forall ${idx} : int :: 0 <= ${idx} && ${idx} < ${ll} ==> ${lname}[${idx}] == ${rname}[${idx}])`;

    return this.boogieString;
}


BoogieExpression.prototype.snapToBoogieOperator = function (op) {
    var result = "";
    switch (op) {
        case "+":
            result = "+";
            break;
        case "−":
            result = "-";
            break
        case "/":
            result = "/";
            break;
        case "×":
            result = "*";
            break;
        case "=":
            result = "==";
            break;
        case "<":
            result = "<";
            break;
        case ">":
            result = ">";
            break;
        case "≤":
            result = "<=";
            break;
        case "≥":
            result = ">=";
            break;
        case "and":
            result = "&&";
            break;
        case "or":
            result = "||";
            break;
        default:
            console.warn(
                "Unknown operator: " + op + ".Returning it as it is.")
            result = "" + op;
    }
    return result;
}

BoogieExpression.prototype.inferTypes = function ( expect ) {
    console.log("Missing infer type for", this);
}


var BoogieMathOp;
BoogieMathOp.prototype = new BoogieExpression();
BoogieMathOp.prototype.constructor = BoogieMathOp;
BoogieMathOp.uber = BoogieExpression.prototype;

function BoogieMathOp(
    block=null, 
    error=false, 
    mssg="",
    arity=0,
    op=null,
    lhs=null, 
    rhs=null)

{    
    this.init(block, error, mssg, arity, op, lhs, rhs);
}

BoogieMathOp.prototype.init = function (
    block, 
    error, 
    mssg, 
    arity, 
    op, 
    lhs, 
    rhs
) {
    var t = new BoogieType(block, _, _, "int")
    BoogieMathOp.uber.init.call(
        this, block, error, mssg, arity, t, op, lhs, rhs);
}

BoogieMathOp.prototype.inferTypes = function (expect) {

    if (expect != null & expect != 'int') {
        this.block.showBubble(`Expected ${expect} but got 'int'.`);
        return null;
    }

    this.lhs.inferTypes('int');
    this.rhs.inferTypes('int');

    return 'int';

}

var BoogieLogicOp;
BoogieLogicOp.prototype = new BoogieExpression();
BoogieLogicOp.prototype.constructor = BoogieLogicOp;
BoogieLogicOp.uber = BoogieExpression.prototype;

function BoogieLogicOp(
    block=null, 
    error=false, 
    mssg="",
    arity=0,
    op=null,
    lhs=null, 
    rhs=null)
{    
    this.init(block, error, mssg, arity, op, lhs, rhs);
}

BoogieLogicOp.prototype.init = function (
    block, error, mssg, arity, op, lhs, rhs
) {
    var t = new BoogieType(block, _, _, "bool")
    BoogieLogicOp.uber.init.call(
        this, block, error, mssg, arity, t, op, lhs, rhs);
}


BoogieLogicOp.prototype.inferTypes = function ( expect ) {

    if (this.arity === 1){

    }else if (this.arity === 2){
        if (this.op.text == "=") {
            let lhst = this.lhs.inferTypes(null);
            let rhst = this.rhs.inferTypes(null);
            if (rhst === null & lhst !== null) {
                rhst = this.rhs.inferTypes(lhst);
            }
            if (lhst === null & rhst !== null) {
                lhst = this.lhs.inferTypes(rhst);
            }
            if (rhst != lhst) {
                this.block.showBubble(
                    `Incompatible types ${lhst} and ${rhst}, for =.`);
            }
        }else if (['>','<'].indexOf(this.op.text) >= 0) {
            this.lhs.inferTypes('int');
            this.lhs.inferTypes('int');
        }else if (['and','or'].indexOf(this.op.text) >= 0) {
            this.lhs.inferTypes('bool');
            this.lhs.inferTypes('bool');
        }
    }
    return 'bool';
}

var BoogieFun;
BoogieFun.prototype = new BoogieExpression();
BoogieFun.prototype.constructor = BoogieFun;
BoogieFun.uber = BoogieExpression.prototype;

function BoogieFun(
    block=null, 
    error=false, 
    mssg="",
    arity=0,
    op=null,
    lhs=null, 
    rhs=null)
{    
    this.init(block, error, mssg, arity, op, lhs, rhs);
}

BoogieFun.prototype.init = function (
    block, error, mssg, arity, op, lhs, rhs
) {
    var t = new BoogieType(block, _, _, "int")
    BoogieFun.uber.init.call(
        this, block, error, mssg, arity, t, op, lhs, rhs);
}

//-------------

var BoogieOld;
BoogieOld.prototype = new BoogieExpression();
BoogieOld.prototype.constructor = BoogieOld;
BoogieOld.uber = BoogieNode.prototype;

function BoogieOld(
    variable=null,
    block=null, 
    error=false, 
    mssg=""
)
{    
    this.init(block, error, mssg, variable);
}

BoogieOld.prototype.init = function (
    block, error, mssg, variable
) {
    this.variable = variable;
    BoogieOld.uber.init.call(this, block, error, mssg);
}

BoogieOld.prototype.compile = function () {
    this.boogieString = "\old(" + this.variable.compile() + ")";
    return this.boogieString;
}

BoogieOld.prototype.get_name = function () {
    return this.variable.get_name();
}

BoogieOld.prototype.inferTypes = function () {
    return BoogieProcedure.get_type(this.variable);
}


//-------------
var BoogieAssertion;

BoogieAssertion.prototype = new BoogieNode();
BoogieAssertion.prototype.constructor = BoogieAssertion;
BoogieAssertion.uber = BoogieNode.prototype;

function BoogieAssertion (assertion, block=null, error=false, mssg="") {
    BoogieAssertion.uber.init.call(this, block, error, mssg);
    this.init(assertion);
}

BoogieAssertion.prototype.init = function (assertion) {
    this.assertion = assertion;
}

BoogieAssertion.prototype.compile = function () {
    this.boogieString = `assert ${this.assertion.compile()};`;
    return this.boogieString;
}

//-------------
var BoogieForall;

BoogieForall.prototype = new BoogieNode();
BoogieForall.prototype.constructor = BoogieForall;
BoogieForall.uber = BoogieNode.prototype;

function BoogieForall (idx, from, to, cond, block=null, error=false, mssg="") {
    BoogieForall.uber.init.call(this, block, error, mssg);
    this.init(idx, from, to, cond);
}

BoogieForall.prototype.init = function (idx, from, to, cond) {
    this.idx = idx;
    this.from = from;
    this.to = to;
    this.cond = cond;
}

BoogieForall.prototype.compile = function () {
    let idx = this.idx.compile();
    let lb = this.from.compile();
    let ub = this.to.compile();
    let cond = this.cond.compile();
    this.boogieString = `(forall ${idx} : int :: (${lb} <= ${idx} && ${idx} <= ${ub}) ==> ${cond})`;
    return this.boogieString;
}

//-------------
var BoogieExists;

BoogieExists.prototype = new BoogieNode();
BoogieExists.prototype.constructor = BoogieExists;
BoogieExists.uber = BoogieNode.prototype;

function BoogieExists (idx, from, to, cond, block=null, error=false, mssg="") {
    BoogieForall.uber.init.call(this, block, error, mssg);
    this.init(idx, from, to, cond);
}

BoogieExists.prototype.init = function (idx, from, to, cond) {
    this.idx = idx;
    this.from = from;
    this.to = to;
    this.cond = cond;
}

BoogieExists.prototype.compile = function () {
    let idx = this.idx.compile();
    let lb = this.from.compile();
    let ub = this.to.compile();
    let cond = this.cond.compile();
    this.boogieString = `(exists ${idx} : int :: (${lb} <= ${idx} && ${idx} <= ${ub}) ==> ${cond})`;
    return this.boogieString;
}

//-------------
var BoogieListInsert;

BoogieListInsert.prototype = new BoogieNode();
BoogieListInsert.prototype.constructor = BoogieListInsert;
BoogieListInsert.uber = BoogieNode.prototype;

function BoogieListInsert (list, idx, item, iidx,block=null, error=false, mssg="") {
    BoogieListInsert.uber.init.call(this, block, error, mssg);
    this.init(list, idx, item, iidx);
}

BoogieListInsert.prototype.init = function (list, idx, item, iidx) {
    this.list = list;
    this.idx = idx;
    this.item = item;
    this.iidx = iidx; // iteration index
}

BoogieListInsert.prototype.compile = function () {
    iidx = this.iidx + "";
    list = this.list + "";
    item = this.item.compile();
    idx = this.idx + "";
    len = compile_list_length(list);

    this.boogieString = `${iidx} := ${idx}-1;\n`;
    this.boogieString += `while(${iidx} < ${len})\n`;
    this.boogieString += `invariant (forall j:int:: j > ${idx}-1 && j < ${iidx} ==> ${list}[j+1] == ${list}[j]);\n{\n`
    this.boogieString += `${list}[${iidx}+1] := ${list}[${iidx}];\n`
    this.boogieString += `${iidx} := ${iidx}+1;\n}\n`;
    this.boogieString += `${len} := ${len}+1;\n`
    this.boogieString += `${list}[${idx}-1] := ${item};`;

    return this.boogieString;
}


//-------------
var BoogieRepeatUntil;

BoogieRepeatUntil.prototype = new BoogieNode();
BoogieRepeatUntil.prototype.constructor = BoogieRepeatUntil;
BoogieRepeatUntil.uber = BoogieNode.prototype;

function BoogieRepeatUntil (cond, inv, body, block=null, error=false, mssg="") {
    BoogieRepeatUntil.uber.init.call(this, block, error, mssg);
    this.init(cond, inv, body);
}

BoogieRepeatUntil.prototype.init = function (cond, inv, body) {
    this.cond = cond;
    this.inv = inv;
    this.body = body;
}

BoogieRepeatUntil.prototype.compile = function () {
    this.boogieString = `while (!${this.cond.compile()})`
    for (x of this.inv) {
        this.boogieString += `\n\t`+ `invariant ${x.compile()};`
    }
    this.boogieString += `\n{`;
    for (x of this.body) {
        this.boogieString += `\n\t` + x.compile();
    }
    this.boogieString += `\n}`;
    return this.boogieString;
}


//-------------

var BoogieIf;

BoogieIf.prototype = new BoogieNode();
BoogieIf.prototype.constructor = BoogieIf;
BoogieIf.uber = BoogieNode.prototype;

function BoogieIf (
    cond, body, block=null, error=false, mssg="") 
{
    BoogieIf.uber.init.call(this, block, error, mssg);
    this.init(cond, body);
}

BoogieIf.prototype.init = function (cond, body, ) {
    this.cond = cond;
    this.body = body;
}

BoogieIf.prototype.compile = function () {
    this.boogieString = `if (${this.cond.compile()}) {`;
    for (x of this.body) {
        this.boogieString += `\n\t${x.compile()}`;
    }
    this.boogieString += `\n}`;
    return this.boogieString;
}

//-------------

var BoogieIfElse;

BoogieIfElse.prototype = new BoogieNode();
BoogieIfElse.prototype.constructor = BoogieIfElse;
BoogieIfElse.uber = BoogieNode.prototype;

function BoogieIfElse (
    cond, ifcase, elsecase, block=null, error=false, mssg="") 
{
    BoogieIfElse.uber.init.call(this, block, error, mssg);
    this.init(cond, ifcase, elsecase);
}

BoogieIfElse.prototype.init = function (cond, ifcase, elsecase) {
    this.cond = cond;
    this.ifcase = ifcase;
    this.elsecase = elsecase;
}

BoogieIfElse.prototype.compile = function () {
    this.boogieString = `if (${this.cond.compile()}) {`;
    for (x of this.ifcase) {
        this.boogieString += `\n\t${x.compile()}`;
    }
    this.boogieString += `\n} else {`;
    for (x of this.elsecase) {
        this.boogieString += `\n\t${x.compile()}`;
    }
    this.boogieString += `\n}`;
    return this.boogieString;
}

//-------------
var BoogieNull;

BoogieNull.prototype = new BoogieNode();
BoogieNull.prototype.constructor = BoogieNull;
BoogieNull.uber = BoogieNode.prototype;

function BoogieNull (block=null, error=false, mssg="") {
    BoogieNull.uber.init.call(this, block, error, mssg);
    this.init();
}

BoogieNull.prototype.init = function () {
    this.boogieString = "null";
}

BoogieNull.prototype.compile = function () {
    return this.boogieString;
}

var BoogieType;
BoogieType.prototype = new BoogieNode();
BoogieType.prototype.constructor = BoogieType;
BoogieType.uber = BoogieNode.prototype;

function BoogieType (block=null, error=false, mssg="", type="") {
    this.init(block, error, mssg, type);
}

BoogieType.prototype.init = function (
    block=null, 
    error=false,
    mssg="",
    type=null) 
{
    BoogieType.uber.init.call(this, block, error, mssg);
    this.type = type;
}

BoogieType.prototype.compile = function () {
    this.boogieString = "" + this.type;
    return this.boogieString;
}

BoogieType.prototype.getType = function () {
    return this.type;
}

//-------------
var BoogieVariableDeclaration;

BoogieVariableDeclaration.prototype = new BoogieNode();
BoogieVariableDeclaration.prototype.constructor = BoogieVariableDeclaration;
BoogieVariableDeclaration.uber = BoogieNode.prototype;

function BoogieVariableDeclaration (block, error, mssg, label) {
    this.init(block, error, mssg, label);
}

BoogieVariableDeclaration.prototype.init = function (
    block, 
    error, 
    mssg, 
    label) 
{
    BoogieVariableDeclaration.uber.init.call(this, block, error, mssg);
    // FIXME we do not use type anymore, we look into the type map
    this.type = null; 
    this.label = label;
}

BoogieVariableDeclaration.prototype.compile = function () {
    if (this.ignore){
        this.boogieString = "";
    }else{
        let name = this.label.get_name();
        let t = BoogieProcedure.get_type(name);
        t = type_to_boogie(t);
        this.boogieString = "var " + name + ": " + t + ";";
    }
    return this.boogieString;
}

BoogieVariableDeclaration.prototype.getName = function () {
    return this.label;
}

BoogieVariableDeclaration.prototype.getType = function () {
    return this.type;
}

BoogieVariableDeclaration.prototype.setType = function (type) {
    this.type = type;
}
//-------------
var BoogieInt;

BoogieInt.prototype = new BoogieNode();
BoogieInt.prototype.constructor = BoogieInt;
BoogieInt.uber = BoogieNode.prototype;

function BoogieInt(block=null, error=false, mssg=""){
    BoogieInt.uber.init.call(this, block, error, mssg);
    this.init();
}

BoogieInt.prototype.init = function(){
    this.value;

}

//-------------
var BoogieReal;

BoogieReal.prototype = new BoogieNode();
BoogieReal.prototype.constructor = BoogieReal;
BoogieReal.uber = BoogieNode.prototype;

function BoogieReal(block=null, error=false, mssg="", value){
    this.init(block=null, error=false, mssg="", value);
}

BoogieReal.prototype.init = function(
    block=null, error=false, mssg="", value){
    BoogieReal.uber.init.call(this, block, error, mssg);
    this.value = value;

}

//-------------
var BoogieLabel;

BoogieLabel.prototype = new BoogieExpression();
BoogieLabel.prototype.constructor = BoogieLabel;
BoogieLabel.uber = BoogieExpression.prototype;

function BoogieLabel (
    block=null, 
    error=false, 
    mssg="", 
    text="", 
    type=null)
{
    this.init(block, error, mssg, text, type);
}

BoogieLabel.prototype.init = function (
    block=null, 
    error=false, 
    mssg="", 
    text="",
    type=null) 
{
    BoogieLabel.uber.init.call(this, block, error, mssg, 0, type);
    this.text = text;
}

BoogieLabel.prototype.compile = function () {
    this.text = "" + this.text;
    this.boogieString = this.error ? this.errorMessage : this.text;
    return this.boogieString;
}

BoogieLabel.prototype.toString = function () {
    return this.text;
}

BoogieLabel.prototype.inferTypes = function (expect) {

    let t = null;

    let num = parseInt(this.text) + "";
    if (!isNaN(num)) {
        t = 'int';
    }else if( this.text === 'false' | this.text === 'true') {
        // it is a boolean
        t = 'bool';
    }else{
        // then it is a label
        t = BoogieProcedure.get_type(this.text);
        if ( t == null) {
            // we may have inferred its type if (expect != null)
            t = expect;
            BoogieProcedure.set_type(this.text, t);
        }
    }

    // check that it is not contradictory with expect
    if (expect !=  null & t != expect) {
        console.error(
            `Expecting type ${expect} but got ${t} for ${this.text}.`);
        this.block.showBubble(
            `Expecting type ${expect} but got type ${t}`);
    }

    return t;
}

BoogieLabel.prototype.get_name = function () {
    return this.text;
}

//-------------
var BoogieBoolean;

BoogieBoolean.prototype = new BoogieNode();
BoogieBoolean.prototype.constructor = BoogieBoolean;
BoogieBoolean.uber = BoogieNode.prototype;

function BoogieBoolean (block=null, error=false, mssg="", value=null){
    BoogieBoolean.uber.init.call(this, block, error, mssg);
    this.init(value);
}

BoogieBoolean.prototype.init = function (
    value = null
) {
    this.value = (typeof value === 'boolean') ? value : null;
}

BoogieBoolean.prototype.compile = function () {
    return "" + this.value;
}

BoogieBoolean.prototype.inferTypes = function (expect) {

    if (expect != null && expect != 'bool') {
        this.block.showBubble(`Expecting ${expect} but got 'bool'`);
    }

    return 'bool';
}

//-------------
var BoogieList;

BoogieList.prototype = new BoogieNode();
BoogieList.prototype.constructor = BoogieList;
BoogieList.uber = BoogieNode.prototype;

function BoogieList (
    block=null, 
    error=false, 
    mssg="",
    id=-1,
    type=null,
    len=0, 
    vals=[])
{
    this.init(block, error, mssg, id, type, len, vals);
}

BoogieList.prototype.init = function (
    block=null, 
    error=false, 
    mssg="",
    id=-1, 
    type=null,
    len=0,
    vals=[]) 
{
    BoogieList.uber.init.call(this, block, error, mssg);
    // this.type = type;
    this.len = len;
    this.vals = vals;
    this.id = id;
    BoogieProcedure.set_type(this.compile_name(), type);
    // this.name = new BoogieLabel(this.block, this.error, this.mssg, name);
}

BoogieList.prototype.compile = function () {
    this.boogieString = "";

    // We build a list of numbers indexed from 0 to to-from.
    let len = this.vals.length;
    let name = this.compile_name();
    var i;
    for (i = 0; i < len; i++) {
        this.boogieString += 
            `\n${name}[${i}] := ${this.vals[i].compile()};`;
    }
    return this.boogieString;
}

BoogieList.prototype.compile_name = function () {
    return "list_" + this.id;
}

BoogieList.prototype.compile_length = function () {
    return this.compile_name() + "_length";
}

BoogieList.prototype.get_name = function () {
    return this.compile_name();
}

function compile_list_length (name) {
    return name + "_length";
}

//-------------
var BoogieRange;

BoogieRange.prototype = new BoogieNode();
BoogieRange.prototype.constructor = BoogieRange;
BoogieRange.uber = BoogieNode.prototype;

function BoogieRange (
    block=null, 
    error=false, 
    mssg="",
    id=-1,
    from=null,
    to=null)
{
    this.init(block, error, mssg, id, from, to);
}

BoogieRange.prototype.init = function (
    block=null, 
    error=false, 
    mssg="",
    id=-1,
    from=null,
    to=null) 
{
    BoogieRange.uber.init.call(this, block, error, mssg);
    this.id = id;
    this.type = 'list int'; // or int? real can operate with other reals.
    let name = this.compile_name();
    BoogieProcedure.typeMap[name] = this.type;
    this.name = new BoogieLabel(this.block,this.error,this.mssg, name);
    this.from = from;
    this.to = to;
}

BoogieRange.prototype.compile_lb = function () {
    return this.from.compile();
}

BoogieRange.prototype.compile_ub = function () {
    return this.to.compile();
}

BoogieRange.prototype.compile = function () {
    // We build a list of numbers indexed from 0 to to-from.
    let idx = this.compile_length();
    let from = this.from.compile();
    let to = this.to.compile();
    let name = this.compile_name();
    if (isNaN(from) | isNaN(to)) {
        this.boogieString = `${idx} := 0;\n` + 
            `while(${idx} <= ${to}-${from})\n\t` + 
            `invariant ${idx} <= ${to}-${from}+1;\n\t` + 
            `invariant (forall i: int ::  0 <= i && i < ${idx} ==>` +
            `${name}[i] == ${from}+i);\n` + 
            `{\n\t${name}[${idx}] := ${from}+${idx};` +
            `\n\t${idx} := ${idx} + 1;\n}\n`;
    } else {
        from = parseInt(from);
        to = parseInt(to);
        let len = to - from + 1;
        let i = 0;
        while( i < len) {
           this.boogieString += `\n${name}[${i}] := ${i+from};`;
           i = i+1;
        }
        this.boogieString += `\n${compile_range_length(name)} := ${len};`;
    }
    return this.boogieString;
}

BoogieRange.prototype.compile_name = function () {
    return `range_${this.id}`;
}

BoogieRange.prototype.compile_length = function () {
    return this.compile_name() + "_length";
}

BoogieRange.prototype.get_name = function () {
    return this.compile_name();
}

function compile_range_length (name) {
    return name + "_length";
}

//-------------
var BoogieMapIndexing;

BoogieMapIndexing.prototype = new BoogieNode();
BoogieMapIndexing.prototype.constructor = BoogieMapIndexing;
BoogieMapIndexing.uber = BoogieNode.prototype;

function BoogieMapIndexing (
    index, list, block=null, error=false, mssg="")
{
    this.init(block,error,mssg,list,index);
}

BoogieMapIndexing.prototype.init = function (
    block=null, 
    error=false, 
    mssg="", 
    list=null,
    index="") 
{
    BoogieMapIndexing.uber.init.call(this, block, error, mssg);    
    this.list = list;
    this.index = index;
}

BoogieMapIndexing.prototype.compile = function () {
    // indexing in Snap! usually start with 1, while we do in 0;
    this.boogieString = 
        `${this.list + ""}[${this.index.compile()}-1]`; 
    return this.boogieString;
}

BoogieMapIndexing.prototype.inferTypes = function (expect) {
    let t = BoogieProcedure.get_type(this.list)
    t = get_inner_type(t)
    // check that it is not contradictory with expect
    if (expect !=  null & t != expect) {
        console.error(
            `Expecting type ${expect} but got ${t} for ${this.text}.`);
        this.block.showBubble(
            `Expecting type ${expect} but got type ${t}`);
    }
    return t;
}

//-------------
var BoogieInput;

BoogieInput.prototype = new BoogieNode();
BoogieInput.prototype.constructor = BoogieInput;
BoogieInput.uber = BoogieNode.prototype;

function BoogieInput (block=null, error=false, mssg="", label=null){
    this.init(block,error,mssg,label);
}

BoogieInput.prototype.init = function (
    block=null, 
    error=false, 
    mssg="", 
    label=null) 
{
    BoogieInput.uber.init.call(this, block, error, mssg);
    this.label = label;
}

BoogieInput.prototype.compile = function () {
    let label = this.label.compile();
    let t = BoogieProcedure.get_type(label);
    this.boogieString = label;
    this.boogieString += this.label.isList ?  `: [int]${t}` : `: ${t}`;
    return this.boogieString;
}

//-------------
var BoogieAssignment;

BoogieAssignment.prototype = new BoogieNode();
BoogieAssignment.prototype.constructor = BoogieAssignment;
BoogieAssignment.uber = BoogieNode.prototype;

function BoogieAssignment (
    block=null, 
    error=false, 
    mssg="", 
    lhs, 
    rhs)
{
    BoogieAssignment.uber.init.call(this, block, error, mssg);
    this.init(lhs, rhs);
}

BoogieAssignment.prototype.init = function (lhs, rhs) {
    this.lhs = lhs;
    this.rhs = rhs;
}

BoogieAssignment.prototype.compile = function () {

    this.boogieString = 
        this.lhs.compile() + " := " + this.rhs.compile() + ";";
    return this.boogieString;
}

BoogieAssignment.prototype.inferTypes = function (expected) {
    // we ignore expected here since this is a command
    
    let t1 = BoogieProcedure.get_type(this.lhs.text, false);
    let t2 = this.rhs.inferTypes(t1);

    if (t1 == null & t2 != null) {
        // console.log("INFERRED type", t2, "for", this.lhs.text);
        BoogieProcedure.set_type(this.lhs.text, t2);
    }

    return null; // We do not expect any type from this inference
}

//-------------
var BoogieReturn;

BoogieReturn.prototype = new BoogieNode();
BoogieReturn.prototype.constructor = BoogieReturn;
BoogieReturn.uber = BoogieNode.prototype;

function BoogieReturn (block=null, error=false, mssg="", ret=null) {
    BoogieReturn.uber.init.call(this, block, error, mssg);
    this.init(ret);
}

BoogieReturn.prototype.init = function (ret = null) {
    if (!(ret instanceof BoogieLabel)){
        this.block.showBubble(
            `Currently, we only allow variables as return values.`);
    } else {
        this.return = ret;
    }
}

BoogieReturn.prototype.compile = function () {

    let ret = this.return.compile();

    this.boogieString = "result := " + ret + ";\n";

    if (this.getType().startsWith("list")) {
        this.boogieString += `\n${compile_list_length('result')}` +
            ` := ${compile_list_length(ret)};`;
    }
    return this.boogieString;
}

BoogieReturn.prototype.getType = function () {
    // return this.return.inferTypes(undefined);
    // We currently not allow formulas in report statements.
    return BoogieProcedure.get_type(this.return.compile());//.get_name());
}

BoogieReturn.prototype.inferTypes = function ( expect) {
    // // we ignore expect since this is a command. Furthermore
    // // if there is already a type for 'result' then we use
    // // it as expect for the inference in this.return .
    // let t1 = BoogieProcedure.get_type('result');
    // let t2 = this.return.inferTypes(null);

    // if (t1 == null) {
    //     // console.log("INFERRED type", t2, "for", 'result');
    //     BoogieProcedure.set_type('result', t2);
    // } 
    // // FIXME: use something else than 'result' so it doesn't clash
    // // with user defined variables

    BoogieProcedure.set_type('result', this.return.inferTypes(null));

    return null;
}

//-------------
var BoogieForEach;

BoogieForEach.prototype = new BoogieNode();
BoogieForEach.prototype.constructor = BoogieForEach;
BoogieForEach.uber = BoogieNode.prototype;

function BoogieForEach (
    block=null, 
    error=false, 
    mssg="", 
    id=-1,
    item=null,
    list=null,
    inva=null,
    body=null) 
{
    this.init(block, error, mssg, id, item, list, inva, body);
}

BoogieForEach.prototype.init = function (
    block=null, 
    error=false, 
    mssg="",
    id=-1,
    item=null,
    list=null,
    inva=null,
    body=null) 
{
    BoogieForEach.uber.init.call(this, block, error, mssg);
    this.id = id;
    this.item = item;
    this.list = list;
    this.inva = inva;
    this.body = body;
}

BoogieForEach.prototype.compile = function () {

    // should be a result of the visitListsPass
    // console.assert(this.list instanceof BoogieLabel, 
    //     `Expecting a BoogieLabel, got ${this.list} instead`);

    let lname = this.list.get_name();
    let t = BoogieProcedure.get_type(lname);
    console.assert(t.startsWith("list"), 
        `Expecting an iterable but got ${t}`);

    let len = compile_list_length(lname);
    let idx = this.compile_index();
    this.boogieString = `${idx} := 0;\n`;

    this.boogieString += 
        `while (${idx} < ${len})`;
    if (this.inva) {
        this.boogieString += `\n\t`+`invariant ${this.inva.compile()};`;
    }   
    this.boogieString += `\n{`;
    for (x of this.body){
        this.boogieString += `\n\t${x.compile()}`; 
    }
    this.boogieString += `\n\t${idx} := ${idx} + 1;\n}`;
    return this.boogieString;
}

BoogieForEach.prototype.compile_index = function () {
    return `loop_${this.id}_index`;
}
/**************************************************************************
 * Helper functions
 *************************************************************************/

function SnapToBoogieType (type) {
    var result = "{{Error: Unknown type}}";
    switch (type) {
        case "#":
            result = "int";
            break;
        case "?":
            result = "bool"; 
            break;
        case ":":
            break;
        default:
            break;
    }
    return result;
}

/**************************************************************************
 * toBoogie methods
 *************************************************************************/

Morph.prototype.toBoogie = function () {
    if (this.isBlockLabelBreak) {
        return null; // skip breaks
    }
    var mssg = "Unimplemented toBoogie Method for: " + this;
    console.warn(mssg);
    return new BoogieNode(this, true, mssg);
}

PrototypeHatBlockMorph.prototype.toBoogie = function () {
    var procedure = new BoogieProcedure(this, false, ""),
        header = null,

    // First the header to get name along with inputs and outputs.
    header = this.children[0].toBoogie();

    procedure.name = header.find( x=>x instanceof BoogieLabel );
    procedure.inputs = header.filter( x=>x instanceof BoogieInput );

    // now the contract
    procedure.requires = this.children[3].toBoogie();
    procedure.ensures = this.children[6].toBoogie();

    // finally the body
    procedure.body = this.children[4].toBoogie();

    return procedure;
}

CustomCommandBlockMorph.prototype.toBoogie = function () {
    " Return a list with the toBoogie() result\
     of each children of this."

    BoogieProcedure.typeMap = {}; // FIXME this is nasty
    
    var result = [];
    for (x of this.children) {
        var r = x.toBoogie();
        if (r) {
            result.push(r);
        }
    }
    return result;
}

CustomReporterBlockMorph.prototype.toBoogie = function () {
    " Return a list with the toBoogie() result\
     of each children of this."

    BoogieProcedure.typeMap = {}; // FIXME this is nasty
    
    var result = [];
    for (x of this.children) {
        var r = x.toBoogie();
        if (r) {
            result.push(r);
        }
    }
    return result;
}


BlockLabelPlaceHolderMorph.prototype.toBoogie = function () {
    return new BoogieNull( this,  false, "");
}

BlockLabelFragmentMorph.prototype.toBoogie = function () {
    return new BoogieLabel(this,  false, "", this.text);
}

BlockInputFragmentMorph.prototype.toBoogie = function () {
    var label = this.children[0].toBoogie();
    console.assert(label instanceof BoogieLabel, 
        "Expecting BoogieLabel got ", label.constructor.name);
    var result = new BoogieInput(this, _, _, label);
    result.type = label.type;
    if (label.type === null) {
        var mssg = "";
        mssg = 
            "Warning, you haven't defined a type for input " + 
            this.children[0].children[0].text +
            ".\n We will try to guess it anyway.";
        this.showBubble(mssg);
    }
    return result;
}

ReporterBlockMorph.prototype.toBoogie = function () {
    var result;
    var n = this.children.length;
    if (n === 1) {
        result = this.children[0].toBoogie(); // a BoogieLabel
    }else if (n === 2) {
        var optor = this.children[0].toBoogie();       
        var opand = this.children[1].toBoogie();
        switch (this.blockSpec) {
            case "not %b":
                result = new BoogieLogicOp(this, _, _, 1, optor, opand);
                break;
            case "list %exp":
                result = [];
                let l = this.children[1].children.length - 1;
                let v = l > 0 ? opand : [];
                let t = l > 0 ? 'list ' + BoogieProcedure.get_type(opand[0]) : 'list int';
                let id = NewId();
                let list = new BoogieList(this, false, "",id,t,l,v);
                BoogieProcedure.set_type(list.get_name(), t);
                result = list;
                break;
            default:
                var spec = this.blockSpec.split(' ');
                switch (spec[1]) {
                    case "?":
                        optor.type = new BoogieType(this, _, _, 'bool');
                        BoogieProcedure.set_type(optor.text, 'bool');
                        result = optor;
                        break;
                    case "#":
                        BoogieProcedure.set_type(optor.text, 'int');    
                        optor.type = new BoogieType(this, _, _, 'int');
                        result = optor;
                        break;
                    case "︙":
                        BoogieProcedure.set_type(optor.text, 'list int');
                        optor.type = null;
                        optor.isList = true;
                        result = optor;
                        break
                    default:
                        console.error("Unknown spec", spec);
                        this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
                        result = null;
                }
        }
    }else if (n === 3) {
        var lhs = this.children[0].toBoogie();
        var op = this.children[1].toBoogie();
        var rhs = this.children[2].toBoogie();

        // FIXME cant match "\old %anyUE" so I patch here
        if (this.blockSpec.includes("old")) {
            result = new BoogieOld(op,this);
            return result;  
        }
        switch(this.blockSpec){
            case "%n + %n":
            case "%n − %n":
            case "%n × %n":
            case "%n / %n":
                result = new BoogieMathOp(this, _, _, 2, op, lhs, rhs);
                break;
            case "%s = %s":
            case "%s < %s":
            case "%s > %s":
            case "%b and %b":
            case "%b or %b":
            case "%s ≥ %s":
            case "%s ≤ %s":
                result = new BoogieLogicOp(this, _, _, 2, op, lhs, rhs);
                break;
            case "%fun of %n":
                result = new BoogieFun(this, _, _, 1, lhs, rhs);
                break;
            case "length of %l":
                result = new BoogieLabel(
                    this,_,_,compile_list_length(rhs.get_name()));
                if (rhs instanceof BoogieOld) {
                    result = new BoogieOld(result)
                }
                break;
            case "\\old %anyUE":
                result = new BoogieOld(op,this);
                break;
            default:
                this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
                result = new BoogieLabel(
                    this, true, "unmatched blockspec@:" + this.blockSpec);
        }
    }else if (n === 4){
        var idx, list;
        switch(this.blockSpec) {
            case "item %idx of %l":
                idx = this.children[1].toBoogie();
                list = this.children[3].toBoogie();
                result = new BoogieMapIndexing(idx, list, this);
                break;
            default:
                this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
                result = new BoogieLabel(
                    this, true, "unmatched blockspec:" + this.blockSpec);
        }
    }else if (n === 5){
        var from, to;
        switch(this.blockSpec) {
            case "numbers from %n to %n":
            case "range from %n to %n":
                from = this.children[2].toBoogie();
                from.type = 'int';
                to   = this.children[4].toBoogie();
                to.type = 'int';
                let id = NewId();
                result = new BoogieRange(this, _, _, id, from, to);
                break;
            case "pick random %n to %n":
                result = this.children[2].toBoogie();
                break;
            default:
                this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
                console.error("Unmatched block spec", this.blockSpec);
        }
    }else if (n === 8){
        var idx, range, cond;
        switch(this.blockSpec) {
            case "Forall %upvar from %s to %s happens %boolUE":
                idx = this.children[1].toBoogie();
                from = this.children[3].toBoogie();
                to = this.children[5].toBoogie();
                cond = this.children[7].toBoogie();
                result = new BoogieForall(idx, from, to, cond, this);
                break;
            default:
                this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
                console.error("Unmatched block spec", this.blockSpec);
        }
    }else if (n === 9){
        var idx, cond;
        switch(this.blockSpec) {
            case "Exists %upvar between %s and %s such that %boolUE":
                idx = this.children[1].toBoogie();
                from = this.children[3].toBoogie();
                to = this.children[5].toBoogie();
                cond = this.children[8].toBoogie();
                result = new BoogieExists(idx, from, to, cond, this);
                break;
            default:
                this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
                console.error("Unmatched block spec", this.blockSpec);
        }
    }else{
        this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
    }
    return result;
}

// function BoogieRange(self, size, start = 0) {
//     return [...Array(size).keys()].map(
//         i => new BoogieLabel(self,_,_,i + start));
// }

MultiArgMorph.prototype.toBoogie = function () {
    // Return a list with the toBoogie() result
    // of each children of this.
    // FIXME: duplicated code see
    // CustomCommandBlockMorph.prototype.toBoogie for instance
    var result = [];
    for (x of this.children) {
        var r = x.toBoogie();
        if (r) {
            result.push(r);
        }
    }
    return result;
}

BooleanSlotMorph.prototype.toBoogie = function () {
    var result;
    if (this.value !== null) {
        result = new BoogieBoolean(this, false, "", this.value);
    }else{
        this.showBubble(
            "Empty (missing value) boolean slot.");
        result = new BoogieBoolean(
            this, 
            true, 
            "Empty (missing value) boolean slot.", 
            null);
    }
    return result;
}

if (!Array.prototype.last){
    Array.prototype.last = function(){
        return this[this.length - 1];
    };
};

CSlotMorph.prototype.toBoogie = function () {
    // Commands inside a CSlot are chained one after the other.
    // We want a list of their boogie interpretation. Furthermore
    // we may get extra boogie commands from nested elements?
    var result = [];
    if (this.children.length > 0) {
        var command = this;
        do {
            command = command.children.last();
            result = result.concat(command.toBoogie());
        } while ( 
            command.children.length > 0 &&
            command.children.last() instanceof CommandBlockMorph
            );
    }
    return result;
}

CommandBlockMorph.prototype.toBoogie = function () {
    var result = [];
    var item, len, list, t, cond, body, idx;
    switch (this.blockSpec) {
        case "script variables %scriptVars":
            let labels = this.children[2].toBoogie();
            for (x of labels) {
                result.push(
                    new BoogieVariableDeclaration(
                        this, 
                        false, 
                        "", 
                        x));
            }
            break;
        case "set %var to %s":
            result = [];
            let lhs = this.children[1].toBoogie();
            let rhs = this.children[3].toBoogie();
            // list assignments is intricate
            if (rhs instanceof BoogieLabel| 
                rhs instanceof BoogieList | 
                rhs instanceof BoogieRange)
            {
                if (rhs instanceof BoogieList | 
                    rhs instanceof BoogieRange) 
                {
                    result.push(rhs);
                    rhs = new BoogieLabel(this,_,_,rhs.get_name());
                }
                let rname = rhs.get_name();
                let t = BoogieProcedure.get_type(rname);
                if (t != null && t.startsWith("list")) {
                    let lname = lhs.get_name();
                    let llen = compile_list_length(lname);
                    let rlen = compile_list_length(rname);
                    BoogieProcedure.set_type(llen, 'int');
                    BoogieProcedure.set_type(lname, 'list int');
                    let llabel = new BoogieLabel(this,_,_,llen);
                    let rlabel = new BoogieLabel(this,_,_,rlen);
                    result.push( new BoogieVariableDeclaration(
                        this,_,_,llabel));
                    result.push( new BoogieAssignment (
                        this, _, _, llabel, rlabel));
                }
            }
            result.push(new BoogieAssignment(
                this,
                false, 
                "", 
                lhs, 
                rhs));
            break;
        case "report %s":
            let ret = this.children[1].toBoogie();
            result = [new BoogieReturn(this, false, "", ret)];
            break;
        case "for each %upvar in %l %br   invariant %boolUE %cla %br   invariant":
            item = this.children[2].toBoogie();
            list = this.children[4].toBoogie();
            let inva = this.children[9].toBoogie();
            body = this.children[10].toBoogie();
            let id = NewId();
            let iterable = list;

            if (list instanceof BoogieList | list instanceof BoogieRange) {
                result.push(list);
                iterable = new BoogieLabel(this,_,_,list.get_name());
            }
            let loop = new 
                BoogieForEach(this, _, _, id, item, iterable, inva, body);
            idx = new BoogieLabel(this,_,_,loop.compile_index());

            result.push(new BoogieVariableDeclaration(this,_,_,idx));
            result.push(new BoogieVariableDeclaration(this,_,_,item));
            BoogieProcedure.set_type(idx.get_name(),'int');
            t = BoogieProcedure.get_type(list.get_name());
            BoogieProcedure.set_type(item.get_name(), get_inner_type(t));
            result.push(loop);
            break;
        case "add %s to %l":
            item = this.children[1].toBoogie();
            list = this.children[3].toBoogie();
            t = BoogieProcedure.get_type(item);
            len = compile_list_length(list.get_name());
            BoogieProcedure.set_type(list.get_name(), `list ${t}`);
            let assign = new BoogieAssignment(this, _, _, 
                new BoogieMapIndexing(len, list, this),
                item);
            let incr = new BoogieAssignment(this, _, _, 
                new BoogieLabel(this, _, _, len),
                new BoogieLabel(this, _, _, len + '+ 1'));
            result = [incr, assign];
            break;
        case "assert %b":
            let assertion = this.children[1].toBoogie();
            result = [new BoogieAssertion(assertion,this)]
            break;
        case "if %b %c":
            cond = this.children[1].toBoogie();
            body = this.children[2].toBoogie();
            result = [new BoogieIf(cond, body, this)];
            break;
        case "if %b %c else %c":
            cond = this.children[1].toBoogie();
            let fst = this.children[2].toBoogie();
            let snd = this.children[4].toBoogie();
            result = [new BoogieIfElse(cond, fst, snd)];
            break;
        case "repeat until %b %br    invariant %mult%b %loop %br    invariant":
            cond = this.children[2].toBoogie();
            inv = this.children[8].toBoogie();
            body = this.children[9].toBoogie();
            result = [new BoogieRepeatUntil(cond, inv, body, this)];
            break;
        case "replace item %idx of %l with %s":
            idx = this.children[2].toBoogie();
            list = this.children[4].toBoogie();
            let val = this.children[6].toBoogie();
            let indexing = new BoogieMapIndexing(idx, list, this);
            result = [new BoogieAssignment(this,_,_,indexing,val)];
            break;
        case "insert %s at %idx of %l":
            item = this.children[1].toBoogie();
            idx = this.children[3].toBoogie();
            list = this.children[5].toBoogie();
            iidx = new BoogieLabel(this,_,_,"iidx_"+NewId());
            result = [];
            result.push(new BoogieVariableDeclaration(this,_,_,iidx));
            result.push(new BoogieListInsert(list,idx,item,iidx,this));
            break;
        default :
            if (['control', 'operators', 'variables'].indexOf(this.category) >= 0){
                this.showBubble("Oops! Don't know how to compile this. Please try some alternative.");
            }
            console.warn("Missing toBoogie case for command " + this);
    }
    return result;
}

TemplateSlotMorph.prototype.toBoogie = function () {
    return this.children[0].toBoogie();
}

StringMorph.prototype.toBoogie = function () {
    var mssg = "",
        error = false,
        text = "",
        type = null,
        result = null;

    if (this.text === "...") {
        mssg = "Missing value at input?";
        this.showBubble(mssg);
        error = true;
    }
    text = this.text;
    type = isNaN(parseInt(this.text)) ? null : 
        new BoogieType(this, _, _, "int");
    result = new BoogieLabel(this, error, mssg, text);
    result.type = type;
    return result;
}

FrameMorph.prototype.toBoogie = function () {
    return null;
}

InputSlotMorph.prototype.toBoogie = function () {
    return this.children[0].toBoogie();
}

/**************************************************************************
 * humanReadable methods for error report
 *************************************************************************/

 // Human readable SyntaxElementMorphs originally for failing 
 // assertion descriptions. 
 
StringMorph.prototype.humanReadable = function () {
    return this.text;
}

SyntaxElementMorph.prototype.humanReadable = function () {
    var result = "";

    result = this.children.filter( 
        function (c) {
            return ! (c instanceof CommandBlockMorph);
        }).map( 
            function (x) { 
                return x.humanReadable() 
            }).join(' ');
    
    return result;
}