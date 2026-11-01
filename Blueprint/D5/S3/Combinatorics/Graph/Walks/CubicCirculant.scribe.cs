using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.Walks;

internal sealed class CubicCirculantDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Every component is an explicit Mobius ladder or Cartesian prism, with the exact gcd multiplicity.", H("All-parameter native cubic-circulant components"), Blocks(
            Paragraph(Text("Let n be even with n at least four, and let 1 at most a be strictly less than n/2. The graph is the actual circulant on ZMod n with differences a, -a and n/2. Write h=gcd(n,a), ell=n/h and g=gcd(a,n/2). These definitions apply to every admissible parameter pair, including disconnected graphs. The finite-walk coset theorem determines actual component supports. Cyclic generator coordinates then determine their graph type.")),
            Node("component_decomposition", "The complete native decomposition",
                And(Eq(C("NatCard",C("Components",C("cubic",I("n"),I("a")))),I("g")),And(Imp(C("Even",I("ell")),And(Eq(I("h"),I("g")),Ex("m",C("Nat"),And(Eq(I("ell"),C("mul",D(2),C("add",I("m"),D(2)))),All("C",C("Components",C("cubic",I("n"),I("a"))),C("GraphIso",C("mobius",I("m")),C("componentGraph",I("C")))))))),Imp(C("Odd",I("ell")),And(C("Even",I("h")),And(Eq(I("g"),C("NatDiv",I("h"),D(2))),Ex("r",C("Nat"),And(Eq(I("ell"),C("add",I("r"),D(3))),All("C",C("Components",C("cubic",I("n"),I("a"))),C("GraphIso",C("prism",I("r")),C("componentGraph",I("C"))))))))))),
                "If ell is even, the antipode is the half-order element of the generator subgroup. Each actual component is therefore M_ell and there are h=g components. If ell is odd, the antipode is outside that subgroup; product coordinates with its order-two subgroup give P_ell. The generator subgroup has odd order, h is even, and there are h/2=g components. Translation constructs the isomorphism to each actual support; none of these graph correspondences is assumed.")), []));
    private static DocumentBlock Node(string name, string title, Formula statement, string explanation) =>
        Describe.Lean(DescribeId.Create(name.Replace('_', '-').ToLowerInvariant()),
            DeclarationHandle.Create("D5/S3/Combinatorics/Graph/Walks/CubicCirculant." + name), H(title),
            StatementSource.FromAuthor(Disp(statement)), AssessedProvenance.FromRepo(),
            Blocks(Paragraph(Text(explanation))),
            name is "mobiusIso" or "pentagon_square_complement_iso" ? DescribeRole.Definition : DescribeRole.Theorem);
    private static Formula I(string s) => F.Id(s);
    private static Formula C(string s, params Formula[] a) => a.Length == 0
        ? new Formula.NamedConstant(FormulaIdentifier.Create(s))
        : new Formula.FunctionCall(FormulaIdentifier.Create(s), [.. a]);
    private static Formula All(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(n), t, b);
    private static Formula Ex(string n, Formula t, Formula b) => new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(n), t, b);
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula And(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.And, b);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(a, FormulaLogicOperator.Implies, b);
}
