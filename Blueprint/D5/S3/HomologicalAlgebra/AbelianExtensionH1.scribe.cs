using static StrataLint.Scribe.DefinitionDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.HomologicalAlgebra;

internal sealed class AbelianExtensionH1Document : IScribeDocumentDefinition
{
    private static readonly LibraryNoteRef Source =
        LibraryNoteRef.Create("D5/L/HomologicalAlgebra/conrad2012groupextensions");

    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Endpoint-fixing automorphisms of an arbitrary abelian group extension, modulo actual kernel conjugations, form its first cohomology group.",
        H("Automorphisms of an abelian extension"),
        Blocks(Describe.Lean(
            DescribeId.Create("abelian-extension-h1-classification"),
            DeclarationHandle.Create("D5/S3/HomologicalAlgebra/AbelianExtensionH1.classification"),
            H("Defects, twists and actual inner automorphisms"),
            StatementSource.WithoutFormula(),
            AssessedProvenance.FromRepo(Source),
            Blocks(
                Paragraph(Text("Let N be any commutative group, Q and S groups, and E an actual short exact sequence 1 to N to Q to S to 1. Write i for its injection and p for its projection. The quotient action on N is descended from conjugation in Q: i(rho(p(y))(n)) = y i(n) y inverse for every y and n. No group section is assumed. The integral representation coefficients E has underlying additive group Additive N and precisely this action.")),
                Paragraph(Text("The subgroup automorphisms E consists of automorphisms of Q that fix i(N) pointwise and induce the identity on S. Its multiplication is ordinary composition. The additive equivalence defectEquiv sends such an automorphism a to the unique cocycle d satisfying i(d(p(y))) = a(y) y inverse for every lift y. The formula holds for every y, so the cocycle is independent of any chosen set-theoretic lift. Conversely its inverse sends d to the automorphism y maps to i(d(p(y))) y. The cocycle relation is d(st) = rho(s)(d(t)) + d(s), which equals the source order because N is commutative. Composition corresponds to cocycle addition, and the inverse twist corresponds to negation.")),
                Paragraph(Text("The homomorphism classMap takes this defect to Mathlib H1. Its kernel innerKernel is characterized exactly by the existence of b in N such that a(y) = i(b) y i(b) inverse for every y. The inner defect is b minus rho(s)(b). Mathlib writes coboundaries as rho(s)(c) minus c; the proof uses c = minus b. Thus the displayed additive quotient is the actual automorphism group modulo actual inner-kernel automorphisms, and is isomorphic as a group to general-action H1.")),
                Paragraph(Text("This statement permits nonsplit extensions, nontrivial actions, infinite groups, arbitrary characteristic and the trivial coefficient group. It does not identify the actual Lambda subgroup of Out(pi), prove the adjusted-representative bridge, establish the finite elementary-abelian consequence, or prove coprime averaging. Those source obligations remain open. No whole theorem or proof atom is closed by this abstract prerequisite.")),
                Paragraph(Text("Conrad section 2.1 states the simply transitive H1 action on the quotient set for arbitrary extensions. The composition-compatible equivalence is established here using the pinned Mathlib extension and cohomology APIs. This is a formal construction of a classical extension-theoretic correspondence, with no claim of literature novelty."))),
            DescribeRole.Theorem))));
}
