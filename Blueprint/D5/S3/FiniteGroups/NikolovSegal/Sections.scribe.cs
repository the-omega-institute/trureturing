using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.FiniteGroups.NikolovSegal;

internal sealed class SectionsDocument : IScribeDocumentDefinition
{

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create("A group section is a surjective image of an arbitrary subgroup; simple sections split across a homomorphism and its kernel.",
        H("Sections of Arbitrary Subgroups"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sections-involves"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Sections.Involves"),
                H("Arbitrary subgroup sections"),
                StatementSource.FromAuthor(Disp(Groups("AG", Iff(I(A,G), Ex("H",C("Subgroup",G),Ex("f",C("Hom",F.Id("H"),A),C("Surjective",f))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Involves(A,G) means that some arbitrary subgroup H of G admits a surjective group homomorphism to A. H need not be normal, and the map need not be defined on all of G. Hom(H,A) denotes the type of group homomorphisms."))),
                DescribeRole.Definition),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sections-involves-of-surjective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Sections.involves_of_surjective"),
                H("A surjective image is a section"),
                StatementSource.FromAuthor(Disp(Groups("AG",All("f",C("Hom",G,A),Imp(C("Surjective",f),I(A,G)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Use the whole group as the section subgroup. This auxiliary statement is used in the kernel branch of the simple-section dichotomy and to prove that the set of alternating degrees is nonempty."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sections-involves-of-injective"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Sections.involves_of_injective"),
                H("Sections pass through embeddings"),
                StatementSource.FromAuthor(Disp(Groups("AGQ",All("i",C("Hom",G,Q),Imp(And(C("Injective",i),I(A,G)),I(A,Q)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("An injective homomorphism carries the section subgroup to its image. Transport its surjection along the induced subgroup isomorphism; this also carries the Sylow-normalizer kernel section to its containing normalizer."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sections-simple-involves-map-or-kernel"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Sections.simple_involves_map_or_kernel"),
                H("A simple section occurs in the image or kernel"),
                StatementSource.FromAuthor(Disp(Groups("AGQ",Imp(C("Simple",A),All("q",C("Hom",G,Q),Imp(I(A,G),Or(I(A,Q),I(A,C("ker",q))))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For a section map from H to a simple group A, the image of the kernel intersection is normal in A. If that image is trivial, the section map descends to the image of H in Q. If it is all of A, the kernel intersection surjects onto A and embeds in the ambient kernel. The homomorphism to Q is arbitrary and need not be surjective."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sections-involves-card-dvd"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Sections.involves_card_dvd"),
                H("Section order divides ambient order"),
                StatementSource.FromAuthor(Disp(Groups("AG",Imp(And(C("Finite",G),I(A,G)),Dvd(C("card",A),C("card",G)))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("For finite G, surjectivity makes the section order divide the subgroup order, and the subgroup order divides the ambient order. The symbol card denotes Nat.card."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sections-not-involves-of-prime-dvd"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Sections.not_involves_of_prime_dvd"),
                H("A divisibility obstruction to sections"),
                StatementSource.FromAuthor(Disp(Groups("AG",Imp(C("Finite",G),All("p",Nat,Imp(And(Dvd(p,C("card",A)),Not(Dvd(p,C("card",G)))),Not(I(A,G)))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Any natural number p dividing the proposed section order but not the finite ambient order excludes that section. Despite the declaration name, this statement does not require p to be prime."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("nikolov-segal-sections-not-involves-pgroup"),
                DeclarationHandle.Create("D5/S3/FiniteGroups/NikolovSegal/Sections.not_involves_pGroup"),
                H("Sections of a p-group are p-groups"),
                StatementSource.FromAuthor(Disp(Groups("AG",All("p",Nat,Imp(And(C("IsPGroup",p,G),Not(C("IsPGroup",p,A))),Not(I(A,G))))))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text("Subgroups and surjective images preserve the p-group property. There is no finiteness or primality hypothesis in this auxiliary obstruction."))),
                DescribeRole.Lemma))));

    private static Formula A => F.Id("A");
    private static Formula G => F.Id("G");
    private static Formula Q => F.Id("Q");
    private static Formula p => F.Id("p");
    private static Formula f => F.Id("f");
    private static Formula i => F.Id("i");
    private static Formula q => F.Id("q");
    private static Formula Nat => F.Id("Nat");
    private static Formula C(string name, params Formula[] args) => new Formula.Apply(F.Id(name), [.. args]);
    private static Formula I(Formula section, Formula group) => C("Involves", section, group);
    private static Formula Dvd(Formula l, Formula r) => new Formula.Relation(l, FormulaRelationOperator.Divides, r);
    private static Formula Imp(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Implies, r);
    private static Formula Iff(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Iff, r);
    private static Formula Or(Formula l, Formula r) => new Formula.Logic(l, FormulaLogicOperator.Or, r);
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
