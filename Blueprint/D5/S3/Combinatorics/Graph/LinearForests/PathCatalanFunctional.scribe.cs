using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Combinatorics.Graph.LinearForests;

internal sealed class PathCatalanFunctionalDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Combinatorics/Graph/LinearForests/PathCatalanFunctional.";
    private static Formula Nat => new Formula.NamedConstant(FormulaIdentifier.Create("Nat"));
    private static Formula All(string name, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), Nat, body);
    private static Formula Le(Formula left, Formula right) =>
        new Formula.Relation(left, FormulaRelationOperator.LessThanOrEqual, right);
    private static Formula Imp(Formula left, Formula right) =>
        new Formula.Logic(left, FormulaLogicOperator.Implies, right);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer alternating Catalan functional on actual independent sets is nonnegative on every finite path at every parameter at least its number of vertices.",
        H("The Catalan functional on paths"),
        Blocks(
            Describe.Lean(DescribeId.Create("functional"),
                DeclarationHandle.Create(Prefix + "phi"),
                H("The finite-domain functional"), StatementSource.WithoutFormula(),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For any vertex type with decidable equality, any simple graph with decidable adjacency, any finite vertex domain V, and any natural parameter m, phi(G,V,m) sums (-1) to the cardinality of S times Catalan(m-card(S)) over every actual independent subset S of V. The result is an integer, and subtraction in the Catalan index is natural subtraction. Applications at m at least card(V) have every index in range. The configurations are the existing hard-core configurations using Mathlib IsIndepSet."))),
                DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("path-nonnegative"),
                DeclarationHandle.Create(Prefix + "path_phi_nonnegative"),
                H("Every legal parameter"),
                StatementSource.FromAuthor(Disp(All("v", All("m", Imp(Le(F.Id("v"), F.Id("m")),
                    Le(D(0), Call("phi", Call("hasse", Nat), Call("range", F.Id("v")), F.Id("m")))))))),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For every pair of natural numbers v and m with v at most m, phi(hasse(Nat),range(v),m) is nonnegative. The finite domain consists of exactly the vertices 0 through v-1 of the natural-number Hasse path; adjacency means consecutive integers. This includes the empty path, m=0, and m=v.")),
                    Paragraph(Text("Let F_v be the sum of (-X) to card(S) over its actual independent configurations, and let C be the Catalan generating series over the integers. The existing independent-set deletion theorem gives F_0=1, F_1=1-X and F_(v+2)=F_(v+1)-X F_v. The existing Catalan equation is X C squared plus one equals C. Induction on v gives F_(v+1) C = F_v + X^(v+2) C^(v+3). At m at least v+1, the coefficient of F_v vanishes. The remaining series is the image under natural-to-integer coefficient casting of X^(v+2) times the corresponding power of the natural Catalan series, so its coefficient is nonnegative. The empty path is the Catalan series itself. No polygon size restriction enters this argument."))),
                DescribeRole.Theorem)), []));
}
