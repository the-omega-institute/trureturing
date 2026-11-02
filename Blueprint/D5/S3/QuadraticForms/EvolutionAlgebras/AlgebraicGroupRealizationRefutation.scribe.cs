using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms.EvolutionAlgebras;

internal sealed class AlgebraicGroupRealizationRefutationDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/EvolutionAlgebras/AlgebraicGroupRealizationRefutation.";
    private static readonly LibraryNoteRef Source = LibraryNoteRef.Create("D5/L/QuadraticForms/kaygorodov2026evolution");
    private const string Question = "Question 31 (Realisation of algebraic groups), page 24: “Let G be a linear algebraic group over 𝕜. Is there a finite-dimensional evolution 𝕜-algebra A with Aut(A) ≅ G(𝕜) as abstract groups? with Aut(A) ≅ G as algebraic groups? with 𝐀𝐮𝐭(A) ≅ G as group schemes?”";
    private static Formula X(string name) => F.Id(name);
    private static Formula Name(string name) => Seq(Operatorname, Grp(X(name)));
    private static Formula Call(string name, params Formula[] args) => new Formula.Apply(Name(name), [.. args]);
    private static Formula All(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), type, body);
    private static Formula Some(string name, Formula type, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), type, body);
    private static Formula Parenthesized(Formula body) => Seq(Open, body, Close);
    private static Formula Arrow(Formula a, Formula b) => Parenthesized(Seq(a, Sp, To, Sp, b));
    private static Formula C => Name("Complex");
    private static Formula ScalarMap => new Formula.Apply(Seq(Name("RingHom"), Dot, Name("id")), [C]);
    private static Formula V => Arrow(Call("Fin", X("d")), C);
    private static Formula Product => Call("LinearMap", ScalarMap, V, Call("LinearMap", ScalarMap, V, V));
    private static Formula ClaimBody() => All("G", Call("LinearAlgebraicGroup", C),
        Some("d", Name("Nat"), Some("mu", Product,
            new Formula.Logic(Call("IsEvolutionAlgebra", X("mu")), FormulaLogicOperator.And,
                Call("Nonempty", Call("Realizes", X("G"), X("mu")))))));
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "SL3 refutes universal realization by full evolution-algebra automorphism functors.",
        H("A negative answer to Question 31 for algebraic groups and group schemes"), Blocks(
            Describe.Lean(DescribeId.Create("claim"), DeclarationHandle.Create(Prefix + "claim"), H("claim"),
                StatementSource.FromAuthor(Disp(new Formula.Relation(Name("claim"), FormulaRelationOperator.Equal, ClaimBody()))),
                AssessedProvenance.FromLiterature(Source), Blocks(Paragraph(Text(Question + " The second and third interrogatives are expressed over Complex using polynomial-closed matrix groups and natural equivalences over every commutative unital Complex-algebra. The source assumes finite dimension unless stated otherwise. The integer d includes zero, the product is arbitrary bilinear multiplication on Fin d → Complex, and IsEvolutionAlgebra supplies an arbitrary natural basis. The first interrogative is outside this assertion."))), DescribeRole.Definition),
            Describe.Lean(DescribeId.Create("result"), DeclarationHandle.Create(Prefix + "result"), H("result"),
                StatementSource.FromAuthor(Disp(Seq(Neg, Sp, Parenthesized(ClaimBody())))),
                AssessedProvenance.FromRepo(Source), Blocks(Paragraph(Text(
                    "For G = slGroup 3, naturality over dual numbers and iterated dual numbers forces the derivation Lie algebra to be sl3. Its dimension is eight and its radical is zero. The semisimple derivation classification of arbitrary finite-dimensional evolution algebras expresses it as a finite sum of orthogonal algebras so(m), m ≥ 3. A summand of dimension at most eight has m = 3 or m = 4 and dimension three or six. A sum of such dimensions is divisible by three and cannot equal eight. This includes products with nonzero annihilator. The comparison between the algebraic-group and group-scheme categories uses characteristic-zero smoothness; the Lean statement uses exactly the full functor formulation. The SLn family outside n = 3, the abstract-group interrogative, positive characteristic, SL2 and SL4 remain outside this theorem. Finite-group, general-linear and orthogonal examples in the survey are unaffected."))), DescribeRole.Theorem,
                new OpenProblemResolutionClaim(ProblemSlugRef.Create("kmvq31"), ResolutionKind.Refuted)))));
}
