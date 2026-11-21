using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.CoxeterMagic;

internal sealed class ElekMagicWordConverseRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/FiniteGroups/CoxeterMagic/ElekMagicWordConverseRefutation.";
    private static readonly LibraryNoteRef Elek =
        LibraryNoteRef.Create("D5/L/FiniteGroups/elek2026magicwords");
    private static readonly LibraryNoteRef BjornerBrenti =
        LibraryNoteRef.Create("D5/L/FiniteGroups/bjornerbrenti2005bruhat");
    private static readonly LibraryNoteRef Umutabazi =
        LibraryNoteRef.Create("D5/L/FiniteGroups/umutabazi2022zircons");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A crystallographic type B₂ Boolean Bruhat interval has no magic word.",
        H("A Boolean Bruhat interval with no magic word"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("elek-magic-word-converse-claim"),
                DeclarationHandle.Create(Prefix + "claim"),
                H("Elek’s Conjecture 3.3"),
                StatementSource.FromAuthor(Disp(ClaimFormula())),
                AssessedProvenance.FromLiterature(Elek),
                Blocks(
                    Paragraph(Text("“A Bruhat interval [v,w] is a hypercube if and only if "
                        + "there exists a magic word Q for [v,w].”")),
                    Paragraph(Text("The Kac–Moody Weyl-group setting is represented by a finite "
                        + "node set and an integral generalized Cartan matrix inducing the Coxeter "
                        + "matrix. The group itself may be infinite. The hypercube predicate asks for "
                        + "a bijection of the full interval with the subsets of a finite set, "
                        + "preserving and reflecting order.")),
                    Paragraph(Text("For Bruhat comparison, a reduced word for the upper element must "
                        + "have a positional subword with the lower product. Björner and Brenti’s "
                        + "subword criterion uses a reduced subword. The deletion condition shortens "
                        + "any retained word to a reduced subword with the same product, so the "
                        + "existence tests coincide. For magicness, Elek counts every positional "
                        + "subword. In sts the masks 000 and 101 both give the identity, and 101 "
                        + "retains the nonreduced word ss. Deletion preserves the existence of a "
                        + "product and can change the number of masks."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("elek-magic-word-converse-result"),
                DeclarationHandle.Create(Prefix + "result"),
                H("The type B₂ counterexample"),
                StatementSource.FromAuthor(Disp(new Formula.Not(F.Id("claim")))),
                AssessedProvenance.FromRepo(Elek, BjornerBrenti, Umutabazi),
                Blocks(
                    Paragraph(Text("Use the canonical presentation with simple reflections s,t "
                        + "and braid exponent four, induced by the type B₂ Cartan matrix. "
                        + "The homomorphism to the dihedral group of order eight sends s and t to "
                        + "two adjacent reflections. Testing words through length three under "
                        + "this map and using a shortest word in the presentation gives "
                        + "length(sts) = 3 and forces sts as its only reduced expression.")),
                    Paragraph(Text("The subword products below sts are e, s, t, st, ts and sts. "
                        + "Exactly s, st, ts and sts are above s. The Bruhat comparisons on "
                        + "these four elements agree in both directions with subset inclusion "
                        + "under the map to the empty set, {0}, {1} and {0,1}, respectively.")),
                    Paragraph(Text("The masks 100 and 001 retain different positions of the "
                        + "only reduced word sts and both give s. The Boolean-to-magic implication "
                        + "therefore fails. Umutabazi uses the same interval for a left-descent "
                        + "criterion. Elek’s Lemma 2.17 gives the related last-letter obstruction "
                        + "to uniqueness even among reduced subwords."))),
                DescribeRole.Theorem))));

    private static Formula ClaimFormula()
    {
        var s = F.Id("S");
        var m = F.Id("M");
        var wGroup = F.Id("W");
        var cs = F.Id("cs");
        var v = F.Id("v");
        var w = F.Id("w");
        var q = F.Id("Q");

        var hasMagicWord = Bind(FormulaQuantifier.Exists, "Q", Call("List", s),
            Call("MagicFor", cs, v, w, q));
        var equivalence = new Formula.Logic(Call("IsHypercube", cs, v, w),
            FormulaLogicOperator.Iff, hasMagicWord);
        Formula body = new Formula.Logic(Call("CartanOrigin", m), FormulaLogicOperator.Implies,
            new Formula.Logic(Call("BruhatLE", cs, v, w), FormulaLogicOperator.Implies,
                Seq(Open, equivalence, Close)));
        body = All("v", wGroup, All("w", wGroup, body));
        body = All("cs", Call("CoxeterSystem", m, wGroup), body);
        body = All("W", F.Id("Type"), Seq(OpenBracket, Call("Group", wGroup), CloseBracket, Sp, body));
        body = All("S", F.Id("Type"), All("M", Call("CoxeterMatrix", s), body));

        return new Formula.Logic(F.Id("claim"), FormulaLogicOperator.Iff, Seq(Open, body, Close));
    }

    private static Formula Call(string name, params Formula[] arguments) =>
        new Formula.Apply(Seq(Operatorname, Grp(F.Id(name))), [.. arguments]);

    private static Formula All(string name, Formula type, Formula body) =>
        Bind(FormulaQuantifier.ForAll, name, type, body);

    private static Formula Bind(FormulaQuantifier quantifier, string name, Formula type, Formula body) =>
        new Formula.BindMany(quantifier, [new Formula.BoundVariable(FormulaIdentifier.Create(name), type)], body);
}
