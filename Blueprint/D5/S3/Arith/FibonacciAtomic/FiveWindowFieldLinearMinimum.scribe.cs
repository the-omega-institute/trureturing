using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.FibonacciAtomic;

internal sealed class FiveWindowFieldLinearMinimumDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/Arith/FibonacciAtomic/FiveWindowFieldLinearMinimum.";
    private static Formula V(string name) => F.Id(name);
    private static Formula Call(string name, params Formula[] args) =>
        new Formula.Apply(Seq(Operatorname, Grp(V(name))), [.. args]);
    private static Formula Par(Formula body) => Seq(Open, body, Close);
    private static Formula EqOf(Formula a, Formula b) => Seq(a, Sp, Eq, Sp, b);
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
        DescribeId.Create("field-window-" + name.ToLowerInvariant()),
        DeclarationHandle.Create(Prefix + name), H(title), StatementSource.WithoutFormula(),
        AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(prose))), DescribeRole.Definition);

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer-induced Fibonacci window responses admit reachable homogeneous realizations over every field.",
        H("Homogeneous Field Realizations of Fibonacci Window Responses"),
        Blocks(
            Paragraph(Text("Let K be any field. Windows null, [2], [3], [25], [5] are read "
                + "high to low, with a seam retaining the previous higher window's low bit. "
                + "An old seam one and a new high bit one are incompatible. The initial seam "
                + "is zero, the composition is (0,0), and the unit bit is zero. Empty words, "
                + "leading null windows and all finite prefixes are included. Integer composition "
                + "is updated first; its output is then mapped coordinatewise from Z to K. "
                + "A legal quantity q has output (1,q), whereas every illegal word has output (0,0).")),
            Definition("SixState", "The two homogeneous seam blocks", "SixState(K)=K^6 has "
                + "coordinates (a_0,b_0,c_0,a_1,b_1,c_1), one three-coordinate block for each seam."),
            Definition("sixUpdate", "Homogeneous affine updates", "For displacement (d_a,d_b), "
                + "an allowed source block (a,b,c) maps to (a+2b+d_a c,2a+3b+d_b c,c) in "
                + "the new seam block. The five displacements are (0,0),(1,0),(0,1),(2,1),(1,1). "
                + "Disallowed source blocks map to zero, and allowed blocks with the same "
                + "destination contribute by addition."),
            Definition("sixTransition", "Linear operators for the windows", "Each homogeneous "
                + "update defines a K-linear endomorphism on the entire six-coordinate space."),
            Definition("sixOutput", "Legality and quantity", "The linear output of x is "
                + "(c_0+c_1,2(a_0+a_1)+3(b_0+b_1)). Legality is retained separately from quantity."),
            Definition("sixDimensional", "The full word representation", "The representation "
                + "has initial vector (0,0,1,0,0,0), window operators sixTransition and output "
                + "sixOutput. The existing chronological wordMap applies letters in input order."),
            Definition("sixEmbed", "Embedding actual integer states", "An actual legal "
                + "integer state occupies only its seam block, with composition mapped from Z "
                + "to K and homogeneous coordinate one. The absorbing error embeds as zero."),
            Definition("sixPrefixes", "Six actual histories", "The prefixes are the empty "
                + "word, [3], [5], [2], [3][2], [5][2], in this order."),
            Describe.Lean(DescribeId.Create("field-window-six-realization"),
                DeclarationHandle.Create(Prefix + "result"), H("All-word correctness and reachable span"),
                StatementSource.FromAuthor(ResultFormula()), AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text("For each field K, F_K denotes sixDimensional(K), f_K "
                        + "denotes integerFieldTask(K), and V_K denotes SixState(K). P_K(j) is "
                        + "the vector reached after prefix j of sixPrefixes, for j in Fin(6). "
                        + "A_K(w) is the reached vector after any finite word w. Realizes(F_K,f_K) "
                        + "means equality of outputs for every finite window word, including illegal words.")),
                    Paragraph(Text("The integer-state embedding commutes with each window "
                        + "operator. Induction on word length transports the complete integer "
                        + "reader to the homogeneous representation. A forbidden seam erases "
                        + "the unique occupied block, and subsequent linear operations preserve zero.")),
                    Paragraph(Text("The first three histories reach (0,0,1),(0,1,1),(1,1,1) "
                        + "in seam zero. Appending [2] gives the three seam-one vectors "
                        + "(1,0,1),(3,3,1),(4,5,1). The six reached columns have determinant "
                        + "minus one, so they form a basis over every field. Consequently the "
                        + "span of all actual reached vectors is the whole state space. This "
                        + "does not assert that each state vector is itself reached by a word."))),
                DescribeRole.Theorem))));

    private static Formula ResultFormula() => Disp(All("K", And(
        Call("Realizes", V("FK"), V("fK")),
        EqOf(Call("dimK", V("VK")), D(6)),
        Call("LinearIndependentK", V("PK")),
        EqOf(Call("spanK", Call("range", V("AK"))), V("VK")))));
}
