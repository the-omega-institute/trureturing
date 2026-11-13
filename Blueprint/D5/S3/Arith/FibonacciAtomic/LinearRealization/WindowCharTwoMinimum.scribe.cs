using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic.LinearRealization;

internal sealed class WindowCharTwoMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/LinearRealization/WindowCharTwoMinimum.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
    private static Formula LeOf(Formula a, Formula b) => Seq(a, Sp, Leq, Sp, b);
    private static Formula Imp(Formula a, Formula b) => Seq(Par(a), Sp, Implies, Sp, Par(b));
    private static Formula All(string name, Formula body) => Seq(Forall, Sp, V(name), Comma, Sp, body);
    private static Formula And(params Formula[] clauses)
    {
        var items = new List<Formula>();
        foreach (var clause in clauses)
        {
            if (items.Count > 0) items.AddRange([Sp, Land, Sp, RowBreak]);
            items.Add(Par(clause));
        }
        return Seq([.. items]);
    }
    private static DocumentBlock Definition(string name, string title, string prose) => Describe.Lean(
        DescribeId.Create("char-two-window-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "The integer-induced five-window task has joint Hankel rank and minimum linear dimension four over every characteristic-two field.",
        H("Characteristic-Two Joint Hankel Rank of Fibonacci Windows"),
        Blocks(
            Paragraph(Text("Let K be any field of characteristic two. The input alphabet consists "
                + "of null, [2], [3], [25] and [5], with low-to-high printed bits 000, 100, 010, "
                + "101 and 001. Words arrive high to low. The preceding higher window's low bit "
                + "cannot meet a one in the incoming window's high bit. The unit bit is zero. "
                + "The task includes the empty word and high-end null padding; an illegal seam "
                + "is absorbing. It is the task of Theorem 8.4 in FIB Relational Continuation "
                + "Geometry.")),
            Paragraph(Text("Use the existing integerFieldTask K: first run the immediate integer "
                + "quantity reader, then apply the canonical integer-to-K map to both outputs. "
                + "A legal composition (a,b) produces (1,2a+3b), reduced in K; error produces "
                + "(0,0). Legal zero therefore produces (1,0). All word products use the existing "
                + "chronological wordMap and WordRepresentation conventions.")),
            Definition("BlockState", "Two seam blocks", "The state space is K^4 with coordinates "
                + "(b_0,c_0,b_1,c_1). The homogeneous coordinate c records legality in its seam block."),
            Definition("blockUpdate", "Reduced affine transitions", "Null and [2] preserve b; "
                + "[3], [25] and [5] add c to b. Each legal source block is sent to the original "
                + "seam destination, and forbidden source blocks contribute zero. Contributions "
                + "are added when the destination is shared. These formulas act on all of K^4."),
            Definition("blockTransition", "Linear letter maps", "Each blockUpdate defines a "
                + "K-linear endomorphism."),
            Definition("blockOutput", "Legality and quantity", "The linear output is "
                + "(c_0+c_1,b_0+b_1), retaining both channels."),
            Definition("fourDimensional", "The four-dimensional representation", "The initial "
                + "vector is (0,1,0,0), letter maps are blockTransition, and the output is blockOutput."),
            Definition("embed", "Integer-state reduction", "An actual integer state with seam s "
                + "and composition (a,b) is placed in block s as (b,1), using the canonical map to K. "
                + "The other block is zero. Error is the zero vector."),
            Definition("channel", "Output selection", "Channel zero selects legality and channel "
                + "one selects quantity through K-linear projections."),
            Definition("jointResidual", "Joint residual responses", "For a two-output task f and "
                + "a prefix u, its joint residual is the single function (v,j) mapping to channel j "
                + "of f(u++v). Both channels share the same prefix and continuation."),
            Definition("jointHankelSpace", "The joint Hankel row space", "Take the K-linear span "
                + "of jointResidual f u over all finite prefixes u inside the function space on "
                + "all continuation-channel pairs. Its dimension is the joint two-output Hankel rank."),
            Definition("futureObservation", "Future observation of an arbitrary state", "For any "
                + "linear word representation R, map a state x to all scalar observations obtained "
                + "by continuing x with v and reading channel j. This is a K-linear map into the "
                + "same continuation-channel function space."),
            Definition("prefixes", "Four actual histories", "The histories are the empty word, "
                + "[3], [2] and [3][2]. They reach both Boolean quantities in both seams."),
            Definition("tests", "Four joint observations", "Read legality and quantity after [5], "
                + "and then legality and quantity after null[5]."),
            Definition("responseMinor", "A joint response minor", "Rows are the four tests and "
                + "columns are the four histories. The entry (i,j) is the selected output after "
                + "history j followed by the continuation in test i. Its rows are (1,1,0,0), "
                + "(1,0,0,0), (1,1,1,1) and (1,0,1,0), and its determinant is one."),
            Describe.Lean(DescribeId.Create("char-two-window-joint-rank-minimum"),
                DeclarationHandle.Create(Prefix + "result"), H("Joint rank and attained minimum"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("In the formula, CharTwoField(K) means that K is a field of "
                        + "characteristic two, fK is integerFieldTask K, FK is fourDimensional K, "
                        + "JK is jointHankelSpace K fK, and K4 is BlockState K. Realizes(R,fK) "
                        + "means equality of both outputs on every finite word. The dimension "
                        + "symbols denote dimension over K. FiniteKSpace(V) asserts that V is a "
                        + "finite-dimensional K-vector space. LinearWordRep(R,V,K) includes its "
                        + "initial vector, linear letter operators and linear output to K^2. "
                        + "No finiteness condition on K and no reachability or observability "
                        + "condition on R is imposed.")),
                    Paragraph(Text("The integer clock sends (a,b) to (a+2b,2a+3b). In "
                        + "characteristic two its second coordinate is b, and the quantity is b. "
                        + "The embedding therefore commutes with each legal affine update and "
                        + "with every error transition. Induction on chronological words gives "
                        + "the all-word realization, including the empty word and illegal words.")),
                    Paragraph(Text("Every joint residual is the future observation of its reached "
                        + "four-dimensional state. Hence the entire residual span lies in the "
                        + "range of one linear map from K^4. This proves finite dimensionality "
                        + "and dimension at most four. Sampling four joint residuals at the four "
                        + "tests gives the determinant-one response matrix, so those residuals "
                        + "are linearly independent and the dimension is exactly four.")),
                    Paragraph(Text("For any competing realization, the same four reached vectors "
                        + "map under its future observations and the same sampling map to the "
                        + "four independent response columns. The reached vectors are therefore "
                        + "linearly independent in the competitor's full state space. Its "
                        + "dimension is at least four, and the explicit K^4 realization attains "
                        + "this bound."))), DescribeRole.Theorem))));

    private static Formula ResultFormula() => Disp(All("K", Imp(Call("CharTwoField", V("K")), And(
        Call("Realizes", V("FK"), V("fK")),
        Call("FiniteDimensional", V("K"), V("JK")),
        EqOf(Call("dim", V("K"), V("JK")), D(4)),
        EqOf(Call("dim", V("K"), V("K4")), D(4)),
        All("V", All("R", Imp(And(Call("FiniteKSpace", V("V")),
            Call("LinearWordRep", V("R"), V("V"), V("K"))),
            Imp(Call("Realizes", V("R"), V("fK")),
                LeOf(D(4), Call("dim", V("K"), V("V")))))))))));
}
