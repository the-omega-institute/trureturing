using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Automata;

internal sealed class DistinguishingFamilyCardinalityBoundDocument : IScribeDocumentDefinition
{
    private const string CardinalityDeclaration = "D5/S0/Automata/DistinguishingFamilyCardinalityBound.card_le_card_output_of_rigid_continuations";
    private const string CertificateDeclaration = "D5/S0/Automata/DistinguishingFamilyCardinalityBound.distinguishing_certificate_bounded_by_output_alphabet";

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Rigid distinguishing continuations are bounded by the output alphabet.",
        H("Rigid Distinguishing Family Cardinality Bound"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("rigid-distinguishing-family-cardinality"),
                DeclarationHandle.Create(CardinalityDeclaration),
                H("A rigid distinguishing family injects into the output alphabet"),
                StatementSource.FromAuthor(CardinalityFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "The types A, O and I range over arbitrary universes. D is a domain of words, T is a total output function, and C is a distinguishing family indexed by I. Fintype denotes a finite-type instance; append is list concatenation.")),
                    Paragraph(Text(
                        "Rigidity is required only for the family's own prefixes and is displayed explicitly. For a nontrivial index type, continuation_constant constructs one continuation shared by all distinct pairs. Evaluating T after that continuation gives an injection into O. The subsingleton case uses the output T of the empty word."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("rigid-distinguishing-certificate-bound"),
                DeclarationHandle.Create(CertificateDeclaration),
                H("The certificate is bounded by both outputs and states"),
                StatementSource.FromAuthor(CertificateFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "S is an arbitrary state type and M is a DFAO over A with outputs in O. In addition to the finite-type instances, the statement requires CorrectOn(M,D,T) and the same explicit rigidity hypothesis.")),
                    Paragraph(Text(
                        "The first conjunct uses the cardinality theorem and its live continuation_constant lemma. The second applies the frozen state_lower_bound_of_distinguishing_family theorem. No rigidity property of powers encodings is asserted here."))),
                DescribeRole.Theorem))));

    private static Formula Call(string name, params Formula[] arguments)
    {
        var items = new List<Formula> { Operatorname, Grp(F.Id(name)), Open };
        for (var index = 0; index < arguments.Length; index++)
        {
            if (index > 0) items.AddRange([Comma, Sp]);
            items.Add(arguments[index]);
        }
        items.Add(Close);
        return Seq([.. items]);
    }

    private static Formula Parameters() => Seq(
        Forall, Sp, F.Id("A"), Comma, Sp, F.Id("O"), Comma, Sp,
        F.Id("I"), Colon, Sp, Call("Type"), Comma,
        RowBreak, Grp(),
        Forall, Sp, F.Id("D"), Colon, Sp, Call("Set", Call("List", F.Id("A"))), Comma, Sp,
        F.Id("T"), Colon, Sp, Call("List", F.Id("A")), Sp, To, Sp, F.Id("O"), Comma,
        RowBreak, Grp(),
        Forall, Sp, F.Id("C"), Colon, Sp,
        Call("DistinguishingFamily", F.Id("D"), F.Id("T"), F.Id("I")), Comma);

    private static Formula RigidFormula() => Seq(
        Open, Forall, Sp, F.Id("i"), Colon, Sp, F.Id("I"), Comma, Sp,
        F.Id("x"), Comma, Sp, F.Id("y"), Colon, Sp, Call("List", F.Id("A")), Comma, Sp,
        Open,
        Call("append", Call("witnessPrefix", F.Id("C"), F.Id("i")), F.Id("x")),
        Sp, InMacro, Sp, F.Id("D"), Sp, Land, Sp,
        Call("append", Call("witnessPrefix", F.Id("C"), F.Id("i")), F.Id("y")),
        Sp, InMacro, Sp, F.Id("D"), Close, Sp, Rightarrow, Sp,
        F.Id("x"), Sp, Eq, Sp, F.Id("y"), Close);

    private static Formula CardinalityFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Parameters(),
        RowBreak, Grp(), Open,
        Call("Fintype", F.Id("I")), Sp, Land, Sp, Call("Fintype", F.Id("O")),
        Sp, Land, Sp, RigidFormula(), Close,
        RowBreak, Grp(), Rightarrow, Sp,
        Call("card", F.Id("I")), Sp, Leq, Sp, Call("card", F.Id("O")), Dot,
        End, Grp(F.Id("gathered"))));

    private static Formula CertificateFormula() => Disp(Seq(
        Begin, Grp(F.Id("gathered")), Parameters(),
        RowBreak, Grp(),
        Forall, Sp, F.Id("S"), Colon, Sp, Call("Type"), Comma, Sp,
        F.Id("M"), Colon, Sp, Call("DFAO", F.Id("A"), F.Id("O"), F.Id("S")), Comma,
        RowBreak, Grp(), Open,
        Call("Fintype", F.Id("I")), Sp, Land, Sp, Call("Fintype", F.Id("O")),
        Sp, Land, Sp, Call("Fintype", F.Id("S")), Sp, Land, Sp,
        Call("CorrectOn", F.Id("M"), F.Id("D"), F.Id("T")),
        Sp, Land, Sp, RigidFormula(), Close,
        RowBreak, Grp(), Rightarrow, Sp, Open,
        Call("card", F.Id("I")), Sp, Leq, Sp, Call("card", F.Id("O")),
        Sp, Land, Sp, Call("card", F.Id("I")), Sp, Leq, Sp, Call("card", F.Id("S")), Close, Dot,
        End, Grp(F.Id("gathered"))));
}
