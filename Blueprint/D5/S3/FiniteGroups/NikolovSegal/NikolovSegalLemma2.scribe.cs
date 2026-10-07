using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class NikolovSegalLemma2Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/FiniteGroups/nikolov2011powers");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("Every normal subgroup of a finite group has a supplement controlling all alternating sections of degree at least five and the largest alternating section degree.",
        H("Nikolov-Segal Lemma 2: Supplements and Alternating Sections"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-nikolovsegallemma2-sylow-normalizer-section-transfer"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.sylow_normalizer_section_transfer"),
                H("Sections descend through the quotient"),
                StatementSource.FromAuthor(Disp(SylowTransferStatement())),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a Sylow p-subgroup P of N, take the normalizer in G of its image under the inclusion of N in G. The kernel of the restricted quotient map embeds in the normalizer of P inside N. The simple-section dichotomy and the Sylow-normalizer obstruction therefore force every indicated section into G/N. The image and normalizer refer to the subgroup inclusion, not a change of section definition."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-nikolovsegallemma2-exists-supplement-preserving-alternating-sections"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.exists_supplement_preserving_alternating_sections"),
                H("One supplement transfers every large alternating section"),
                StatementSource.FromAuthor(Disp(SupplementTransferStatement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("Choose a Sylow 2-subgroup P of N and let L be the normalizer in G of its image. Frattini gives N join L equal to G. For every k at least five, Alt(k) is simple, has even order, and is not a 2-group, so its sections in L descend to G/N. The existential quantifier for L precedes the universal quantifier for k: the same supplement works for all such degrees."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-nikolovsegallemma2-exists-supplement-alpha-le"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/NikolovSegalLemma2.exists_supplement_alpha_le"),
                H("The exact largest-degree inequality"),
                StatementSource.FromAuthor(Disp(AlphaSupplementStatement())),
                AssessedProvenance.FromLiterature(Source),
                Blocks(Paragraph(Text("This is Powers in finite groups, printed page 504, Lemma 2. Use the same Sylow-normalizer supplement as in the section-transfer theorem and apply the attained maximum characterization of alpha. All finite groups and all normal subgroups are allowed, including the bottom and top normal subgroups. This structural lemma does not by itself establish the power-width, restricted Burnside, or profinite strong-completeness targets."))),
                DescribeRole.Theorem))));

    private static Formula SylowTransferStatement()
    {
        Formula normalizer = C("normalizer", C("image", P, C("inclusion", N)));
        Formula body = Imp(And(Not(C("IsPGroup", p, A)), Dvd(p, C("card", A)),
            I(A, normalizer)), I(A, C("Quotient", G, N)));
        body = All("P", C("Sylow", p, N), body);
        body = All("p", Nat, Imp(C("Prime", p), body));
        body = All("N", C("Subgroup", G), Imp(C("Normal", N), body));
        return Groups("AG", Imp(And(C("Finite", G), C("Simple", A)), body));
    }

    private static Formula SupplementTransferStatement()
    {
        Formula transfer = All("k", Nat,
            Imp(And(Le(new Formula.Number(5), k), I(Alt(k), L)), I(Alt(k), C("Quotient", G, N))));
        Formula body = Ex("L", C("Subgroup", G), And(Eq(C("join", N, L), Top), transfer));
        body = All("N", C("Subgroup", G), Imp(C("Normal", N), body));
        return Groups("G", Imp(C("Finite", G), body));
    }

    private static Formula AlphaSupplementStatement()
    {
        Formula bound = Le(C("alpha", L), C("max", C("alpha", C("Quotient", G, N)), new Formula.Number(4)));
        Formula body = Ex("L", C("Subgroup", G), And(Eq(C("join", N, L), Top), bound));
        body = All("N", C("Subgroup", G), Imp(C("Normal", N), body));
        return Groups("G", Imp(C("Finite", G), body));
    }

    private static Formula A => F.Id("A");
    private static Formula G => F.Id("G");
    private static Formula N => F.Id("N");
    private static Formula L => F.Id("L");
    private static Formula P => F.Id("P");
    private static Formula p => F.Id("p");
    private static Formula k => F.Id("k");
    private static Formula Nat => F.Id("Nat");
    private static Formula Top => F.Id("top");
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula I(Formula section, Formula group) => C("Involves", section, group);
    private static Formula Alt(Formula degree) => C("alternatingGroup", C("Fin", degree));
    private static Formula Eq(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Equal, r);
    private static Formula Le(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.LessThanOrEqual, r);
    private static Formula Dvd(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Divides, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Not(Formula body) => new Formula.Not(body);
    private static Formula And(Formula first, params Formula[] rest)
    {
        Formula result = first;
        foreach (Formula next in rest) result = new Formula.Logic(result, FormulaLogicOperator.And, next);
        return result;
    }
    private static Formula All(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.ForAll, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula Ex(string name, Formula domain, Formula body) => new Formula.BindMany(
        FormulaQuantifier.Exists, [new Formula.BoundVariable(FormulaIdentifier.Create(name), domain)], body);
    private static Formula OneGroup(string name, string universe, Formula body) =>
        All(name, F.Id(universe), Imp(C("Group", F.Id(name)), body));
    private static Formula Groups(string names, Formula body) => names switch
    {
        "G" => OneGroup("G", "Typev", body),
        "AG" => OneGroup("A", "Typeu", OneGroup("G", "Typev", body)),
        "GQ" => OneGroup("G", "Typev", OneGroup("Q", "Typew", body)),
        "AGQ" => OneGroup("A", "Typeu", OneGroup("G", "Typev", OneGroup("Q", "Typew", body))),
        _ => body,
    };
}
