using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Quantum.Entanglement.GraphDensity;

internal sealed class SelectiveFormationBoundsDocument : IScribeDocumentDefinition
{
    private const string Module = "D5/S3/Quantum/Entanglement/GraphDensity/SelectiveFormationBounds.";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Coordinate-block formation lower bound and exact embedding.",
        H("SelectiveFormationBounds"),
        Blocks(
            Paragraph(Text("Scalar quotients are real unless a complex cast is displayed. Fin indices are zero based. Matrix, rankOneDensity, partialTraceRight and partialTransposeB denote the actual Lean operations. All entropy values are in bits.")),
            Describe.Lean(DescribeId.Create("pairequiv"),
                DeclarationHandle.Create(Module + "pairEquiv"), H("pairEquiv"),
                StatementSource.FromAuthor(Disp(All(F.Id("k"), Seq(Mathbb, Sp, F.Id("N")), Seq(Call("pairEquiv", F.Id("k")), Eq, Apply(Seq(Seq(Operatorname, Grp(F.Id("finProdFinEquiv"))), Dot, Seq(Operatorname, Grp(F.Id("trans")))), Call("finCongr", Apply(Qualified("Nat", "mul_comm"), F.Id("k"), D(2)))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("The literal Lean expression is finProdFinEquiv.trans (finCongr (Nat.mul_comm k 2)); the equality proof only casts k·2 to 2·k."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("pairequiv-val"),
                DeclarationHandle.Create(Module + "pairEquiv_val"), H("pairEquiv_val"),
                StatementSource.FromAuthor(Disp(All(F.Id("k"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("j"), Call("Fin", F.Id("k")), All(F.Id("b"), Call("Fin", D(2)), Seq(Call("val", Apply(Call("pairEquiv", F.Id("k")), Parenthesized(Seq(F.Id("j"), Comma, F.Id("b"))))), Eq, Seq(Call("val", F.Id("b")), Plus, Seq(D(2), Cdot, Sp, Call("val", F.Id("j")))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Literal Lean theorem; every displayed parameter is quantified."))), DescribeRole.Theorem),
            Describe.Lean(DescribeId.Create("embedstate"),
                DeclarationHandle.Create(Module + "embedState"), H("embedState"),
                StatementSource.FromAuthor(Disp(All(F.Id("k"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("j"), Call("Fin", F.Id("k")), All(Rho, Call("Matrix", Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", D(2)))), Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", D(2)))), Seq(Mathbb, Sp, F.Id("C"))), All(F.Id("x"), Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", Seq(D(2), Cdot, Sp, F.Id("k"))))), All(F.Id("y"), Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", Seq(D(2), Cdot, Sp, F.Id("k"))))), Seq(Apply(Call("embedState", F.Id("j"), Rho), F.Id("x"), F.Id("y")), Eq, Call("ite", Seq(Parenthesized(Seq(Seq(Apply(Seq(Call("pairEquiv", F.Id("k")), Dot, Named("symm")), Seq(F.Id("x"), Dot, D(2))), Dot, D(1)), Eq, F.Id("j"))), Land, Sp, Parenthesized(Seq(Seq(Apply(Seq(Call("pairEquiv", F.Id("k")), Dot, Named("symm")), Seq(F.Id("y"), Dot, D(2))), Dot, D(1)), Eq, F.Id("j")))), Apply(Rho, Parenthesized(Seq(Seq(F.Id("x"), Dot, D(1)), Comma, Seq(Apply(Seq(Call("pairEquiv", F.Id("k")), Dot, Seq(Operatorname, Grp(F.Id("symm")))), Seq(F.Id("x"), Dot, D(2))), Dot, D(2)))), Parenthesized(Seq(Seq(F.Id("y"), Dot, D(1)), Comma, Seq(Apply(Seq(Call("pairEquiv", F.Id("k")), Dot, Seq(Operatorname, Grp(F.Id("symm")))), Seq(F.Id("y"), Dot, D(2))), Dot, D(2))))), D(0)))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Literal Lean definition; every displayed parameter is quantified."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("embedded-formation-lower"),
                DeclarationHandle.Create(Module + "embedded_formation_lower"), H("embedded_formation_lower"),
                StatementSource.FromAuthor(Disp(All(F.Id("k"), Seq(Mathbb, Sp, F.Id("N")), All(F.Id("j"), Call("Fin", F.Id("k")), All(Rho, Call("Matrix", Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", D(2)))), Seq(Parenthesized(Call("Fin", D(2))), Times, Sp, Parenthesized(Call("Fin", D(2)))), Seq(Mathbb, Sp, F.Id("C"))), Seq(Parenthesized(Call("Nonempty", Call("Ensemble", Call("embedState", F.Id("j"), Rho)))), Longrightarrow, Sp, Seq(Apply(Seq(F.Id("E"), Underscore, F.Id("F")), Rho), Le, Sp, Apply(Seq(F.Id("E"), Underscore, F.Id("F")), Call("embedState", F.Id("j"), Rho))))))))),
                AssessedProvenance.FromRepo(LibraryNoteRef.Create("D5/L/QuantumStates/braunstein2006laplaciandensity")),
                Blocks(Paragraph(Text("Compressing an ensemble supported in a single coordinate block preserves its pure marginal entropy; taking the infimum gives the lower bound."))), DescribeRole.Theorem))));

    private static Formula Parenthesized(Formula value) => Seq(Open, value, Close);
    private static Formula Apply(Formula function, params Formula[] arguments) =>
        Seq(function, Parenthesized(Join(arguments)));
    private static Formula Join(Formula[] arguments) => arguments.Length switch
    {
        0 => Seq(),
        1 => arguments[0],
        _ => Seq(arguments[0], Comma, Join(arguments[1..]))
    };
    private static Formula Qualified(string owner, string name) =>
        Seq(Operatorname, Grp(F.Id(owner)), Dot, Named(name));
    private static Formula Named(string name) => name.Contains('_')
        ? Seq(Operatorname, Grp(F.Id(name.Split('_')[0])), Underscore, Grp(F.Id(name.Split('_')[1])))
        : Seq(Operatorname, Grp(F.Id(name)));
    private static Formula All(Formula variable, Formula type, Formula body) =>
        Seq(Forall, Sp, Parenthesized(Seq(variable, Colon, type)), Comma, Sp, body);

}
