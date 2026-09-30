using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Fourier.CharacterSelection;

internal sealed class SignedIncidenceTotalUnimodularityDocument : IScribeDocumentDefinition
{
    private const string Prefix =
        "D5/S3/Fourier/CharacterSelection/SignedIncidenceTotalUnimodularity.";
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/Combinatorics/vondrak2017totalunimodularity");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Integer signed endpoint boundaries are totally unimodular for arbitrary parallel directed edges and loops.",
        H("Integer Signed Incidence Boundaries are Totally Unimodular"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("signed-incidence-definition"),
                DeclarationHandle.Create(Prefix + "signedIncidence"),
                H("The integer signed endpoint incidence matrix"),
                StatementSource.FromAuthor(DefinitionFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text(
                    "For arbitrary vertex and edge types, each column records one positive head endpoint "
                        + "and one negative tail endpoint. A loop therefore gives a zero column, while "
                        + "parallel edge labels remain separate columns."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("signed-incidence-totally-unimodular"),
                DeclarationHandle.Create(Prefix + "signed_incidence_is_totally_unimodular"),
                H("Every finite minor has determinant minus one, zero, or one"),
                StatementSource.FromAuthor(TheoremFormula()),
                AssessedProvenance.FromLiterature(Source),
                Blocks(
                    Paragraph(Text(
                        "For every natural minor order k, every injective row selection f from Fin k to V, "
                            + "and every injective column selection g from Fin k to E, the determinant of "
                            + "the selected signed incidence minor belongs to {-1, 0, 1}. No finiteness, "
                            + "simplicity, loop-free, connectedness, or orientation restriction is imposed.")),
                    Paragraph(Text(
                        "The proof inducts on the minor order. A loop or a selected column with a missing "
                            + "endpoint is handled by Laplace expansion and the induction hypothesis. If every "
                            + "selected column has two distinct selected endpoints, the sum of the selected rows "
                            + "is zero, so the determinant vanishes. The zero-order minor has determinant one.")),
                    Paragraph(Text(
                        "This is literature-attested from Vondrak's MATH233B Lecture 3, Lemma 10, and is "
                            + "formalized here with the stronger arbitrary endpoint presentation. It does not "
                            + "claim flow integrality or a matrix-tree theorem."))),
                DescribeRole.Theorem)),
        []));

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.FunctionCall(FormulaIdentifier.Create(name), [.. arguments]);

    private static Formula TypeUniverse() => Seq(Operatorname, Grp(F.Id("Type")));

    private static Formula DefinitionFormula()
    {
        Formula vertex = F.Id("v"), edge = F.Id("e");
        Formula tail = F.Id("tail"), head = F.Id("head");
        Formula headValue = new Formula.Subscript(
            Seq(Mathbf, Grp(D(1))),
            Grp(new Formula.Relation(vertex, FormulaRelationOperator.Equal, Call("head", edge))));
        Formula tailValue = new Formula.Subscript(
            Seq(Mathbf, Grp(D(1))),
            Grp(new Formula.Relation(vertex, FormulaRelationOperator.Equal, Call("tail", edge))));
        Formula value = Seq(
            headValue, Sp, Minus, Sp, tailValue);
        return Disp(Seq(
            Call("signedIncidence", tail, head, vertex, edge), Sp, Eq, Sp, value, Sp, InMacro, Sp,
            Seq(Mathbb, Grp(F.Id("Z"))), Dot));
    }

    private static Formula TheoremFormula()
    {
        Formula V = F.Id("V"), E = F.Id("E"), k = F.Id("k");
        Formula f = F.Id("f"), g = F.Id("g"), tail = F.Id("tail"), head = F.Id("head");
        Formula matrix = Call("signedIncidence", tail, head);
        Formula minor = Call("det", Call("submatrix", matrix, f, g));
        Formula finToV = new Formula.TypeArrow(Call("Fin", k), V);
        Formula finToE = new Formula.TypeArrow(Call("Fin", k), E);
        Formula quantifiers = Seq(
            Forall, Sp, V, Colon, Sp, TypeUniverse(), Comma, Sp,
            Forall, Sp, E, Colon, Sp, TypeUniverse(), Comma, Sp,
            OpenBracket, Call("DecidableEq", V), CloseBracket, Comma, Sp,
            Forall, Sp, tail, Comma, Sp, head, Colon, Sp, new Formula.TypeArrow(E, V), Comma, Sp,
            Forall, Sp, k, Colon, Sp, Seq(Mathbb, Grp(F.Id("N"))), Comma, Sp,
            Forall, Sp, f, Colon, Sp, finToV, Comma, Sp,
            Forall, Sp, g, Colon, Sp, finToE, Comma, Sp,
            Call("Injective", f), Sp, Rightarrow, Sp,
            Call("Injective", g), Sp, Rightarrow, Sp,
            minor, Sp, InMacro, Sp,
            Seq(OpenBrace, Minus, D(1), Comma, Sp, D(0), Comma, Sp, D(1), CloseBrace));
        return Disp(quantifiers);
    }
}
