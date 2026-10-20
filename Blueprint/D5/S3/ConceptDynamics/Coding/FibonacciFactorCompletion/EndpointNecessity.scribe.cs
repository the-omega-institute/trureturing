using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class EndpointNecessityDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/EndpointNecessity.";
    private static Formula.BoundVariable B(string name, Formula type) =>
        new(FormulaIdentifier.Create(name), type);
    private static Formula All(Formula body, params Formula.BoundVariable[] variables) =>
        new Formula.BindMany(FormulaQuantifier.ForAll, [.. variables], body);
    private static Formula And(params Formula[] clauses)
    {
        var result = clauses[^1];
        for (var i = clauses.Length - 2; i >= 0; --i)
            result = new Formula.Logic(clauses[i], FormulaLogicOperator.And, result);
        return result;
    }
    private static Formula I(string name) => F.Id(name);

    private static Formula Imp(Formula a,Formula b) => new Formula.Logic(a,FormulaLogicOperator.Implies,b);
    private static Formula Fn(Formula a,Formula b) => Call("Function",a,b);

private static Formula OriginalFixedTailEndpointBudget()
{
    var u=I("U");var v=I("V");var w=I("W");var length=I("L");var b=I("b");
    var ui=Call("apply",u,I("i"));var vi=Call("apply",v,I("i"));var wi=Call("apply",w,I("i"));
    var highPrefix=Call("append",I("P"),Call("choiceBlocks",u,I("zs")));
    var lowPrefix=Call("append",I("Q"),Call("choiceBlocks",v,I("zs")));
    var colors=Call("append",I("h"),Call("choiceBlocks",w,I("zs")));
    var theta=Call("familyEndpointBudget",I("P"),I("Q"),I("h"),u,v,w,length);
    var data=And(Equal(Call("length",I("P")),Call("length",I("h"))),
        Equal(Call("length",I("Q")),Call("length",I("h"))),Call("lt",D(0),length),
        All(And(Equal(Call("length",ui),length),Equal(Call("length",vi),length),
            Equal(Call("length",wi),length),Call("LegalWord",I("s1"),I("s1"),ui),
            Call("LegalWord",I("s2"),I("s2"),vi)),B("i",I("Bool"))),
        Call("le",D(0),b),
        All(And(Call("ClosedOriginalTailExtension",b,highPrefix,colors,I("xi"),I("x"),I("path1")),
            Call("ClosedOriginalTailExtension",b,lowPrefix,colors,I("eta"),I("y"),I("path2"))),
            B("zs",Call("List",I("Bool")))));
    return Disp(All(Imp(data,And(Call("le",theta,b),Call("member",theta,I("coefficientField")))),
        B("s1",I("Guard")),B("s2",I("Guard")),B("P",Call("List",I("Label"))),
        B("Q",Call("List",I("Label"))),B("h",Call("List",I("Color"))),
        B("U",Fn(I("Bool"),Call("List",I("Label")))),B("V",Fn(I("Bool"),Call("List",I("Label")))),
        B("W",Fn(I("Bool"),Call("List",I("Color")))),B("L",I("Nat")),
        B("xi",Fn(I("Nat"),I("Label"))),B("eta",Fn(I("Nat"),I("Label"))),
        B("x",Fn(I("Nat"),I("Real"))),B("y",Fn(I("Nat"),I("Real"))),
        B("path1",Fn(I("Nat"),I("Guard"))),B("path2",Fn(I("Nat"),I("Guard"))),B("b",I("Real"))));
}


    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The same full actual tails across every finite history force the original six-group endpoint budget in Q(t).",
        H("Fixed-tail endpoint-budget necessity"),
        Blocks(
Describe.Lean(DescribeId.Create("fib-original-fixed-tail-endpoint-budget"),
    DeclarationHandle.Create(Prefix+"original_fixed_tail_endpoint_budget"),
    H("Every fixed actual tail obeys the complete endpoint budget"),
    StatementSource.FromAuthor(OriginalFixedTailEndpointBudget()),AssessedProvenance.FromRepo(),
    Blocks(
        Paragraph(Text("ClosedOriginalTailExtension(b,A,cs,xi,x,path) means there exist full literal, scalar and guard sequences a,X,q starting at guard G0, following every original nextGuard edge, supported at every position, and satisfying X(p)=branch(a(p),X(p+1)). The first length(A) labels equal A. At length(A)+p all three future sequences equal respectively xi(p),x(p),path(p), for every p. Only departures r<length(cs) satisfy ClosedExpanded(b,cs[r],X(r)). The theorem makes the observed source and color lengths equal. ClosedExpanded(b,c,z) is the original closed relaxation z in [-1,phi], cut(c)-b<=z<=cut(c+1)+b.")),
        Paragraph(Text("The same two full futures are fixed before every finite Boolean choice word, including the empty word. Their starting scalars need not belong to either canonical hull. For each component, the existing canonical periodic endpoint supplies one repeated extremal return when (-g)^L is positive, or two alternating extremal returns when it is negative. Finite repetitions act on the original fixed scalar. The existing signed orbit criterion, applied to the closed affine preimage of one slot constraint, forces that endpoint to satisfy the slot. Stem slots use the extremal choice history directly; each return slot uses its chosen first return followed by that history. Both endpoints of every one of the six indexed groups are included. Different endpoint tests may use different histories under the universal premise.")),
        Paragraph(Text("familyEndpointBudget is the existing foldr max 0 of familyEndpointCosts, with exactly two stem groups and all four return groups. Equal-valued entries are retained. Original suffix evaluations, all cut values and canonical endpoints belong to coefficientField=Q(t); every finite maximum selects one of its arguments. Each endpoint cost is at most the supplied nonnegative b, so the whole maximum is at most b and belongs to that field. Empty stems, singleton hulls, equal returns, either slope sign and b=0 are included. This necessary bound does not require U(false)!=U(true); the original source-separation requirements remain in the separate original goal.")),
        Paragraph(Text("This is necessity for the closed relaxation. It asserts neither ownership-sensitive color attainment at equality, nor a new decoder-capacity or optional-piece result. No terminal color is tested. The high and low futures may differ. No budget infimum over a changing family of tails replaces the original fixed-tail quantifiers."))),
    DescribeRole.Theorem))));
}
