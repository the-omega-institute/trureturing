using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.ConceptDynamics.Coding.FibonacciFactorCompletion;

internal sealed class CanonicalGeometryDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/ConceptDynamics/Coding/FibonacciFactorCompletion/CanonicalGeometry.";
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
    private static Formula CanonicalLegalReturnHull()
    {
        var u=I("U");var length=I("L");var s=I("s");var i=I("i");var z=I("z");
        var lo=Call("canonicalReturnLo",u,length);var hi=Call("canonicalReturnHi",u,length);
        var word=Call("apply",u,i);var image=Call("compose",word,z);
        Formula Invariant(Formula lower,Formula upper) =>
            All(Imp(And(Call("le",lower,z),Call("le",z,upper)),
                And(Call("le",lower,image),Call("le",image,upper))),B("i",I("Bool")),B("z",I("Real")));
        var data=And(Call("lt",D(0),length),
            All(Equal(Call("length",word),length),B("i",I("Bool"))),
            All(Call("LegalWord",s,s,word),B("i",I("Bool"))));
        var result=And(Call("le",lo,hi),
            Imp(Call("notEqual",Call("apply",u,I("false")),Call("apply",u,I("true"))),Call("lt",lo,hi)),
            All(Imp(And(Call("le",lo,z),Call("le",z,hi)),Call("InSupport",s,z)),B("z",I("Real"))),
            Invariant(lo,hi),
            All(Imp(And(Call("le",I("l"),I("upper")),Invariant(I("l"),I("upper"))),
                And(Call("le",I("l"),lo),Call("le",hi,I("upper")))),B("l",I("Real")),B("upper",I("Real"))),
            new Formula.Logic(Equal(lo,hi),FormulaLogicOperator.Iff,
                Equal(Call("apply",u,I("false")),Call("apply",u,I("true")))),
            And(Call("member",lo,I("coefficientField")),Call("member",hi,I("coefficientField"))));
        return Disp(All(Imp(data,result),B("s",I("Guard")),
            B("U",Fn(I("Bool"),Call("List",I("Label")))),B("L",I("Nat"))));
    }

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Both actual Fibonacci starts retain the complete-boundary, closed and strict source laws and one finite actual reset map.",
        H("Actual boundaries for Fibonacci completion"),
        Blocks(
            Describe.Lean(DescribeId.Create("fib-canonical-legal-return-hull"),
                DeclarationHandle.Create(Prefix+"canonical_legal_return_hull"),
                H("Actual legal returns determine their canonical hull"),
                StatementSource.FromAuthor(CanonicalLegalReturnHull()),AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Write A(i)=compose(U(i),0), a=(-g)^L, Amin=min(A(false),A(true)), and Amax=max(A(false),A(true)). The common return length L is positive. canonicalReturnLo and canonicalReturnHi use (Amin/(1-a),Amax/(1-a)) when a>0, and ((Amin+a*Amax)/(1-a^2),(Amax+a*Amin)/(1-a^2)) when a<0. The literal slope has nonzero absolute value less than one. The width is respectively (Amax-Amin)/(1-a) or (Amax-Amin)/(1+a).")),
                    Paragraph(Text("Both words return legally from s to s. The displayed interval is nonempty, lies in the actual guard support, is invariant under each full return, and is contained in every nonempty invariant closed interval [l,upper]. Distinct equal-length words have distinct zero-tail scalar values: all finite suffixes at zero lie strictly inside their actual guard supports, and root branch interiors from one guard are disjoint. Induction then recovers the labels and full words from equal scalars. Literal return difference therefore gives strict hull width. The notEqual predicate in the displayed statement denotes literal inequality.")),
                    Paragraph(Text("The statement permits equal words and a singleton hull. It does not identify the interval with the attractor. The singleton-hull equivalence is literal word equality. coefficientField is the intersection of all real subfields containing t, hence the original Q(t). Both computed endpoints belong to this field. The specified periodic endpoint addresses are supplied separately by canonical_periodic_endpoints."))),DescribeRole.Theorem))));
}
