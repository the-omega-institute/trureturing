using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S0.Computability.Diophantine;

internal sealed class DiophantineIntegerToRationalDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "A finite polynomial definition of the integers yields a joint-assignment solvability reduction.",
        H("Conditional Integer-to-Rational Polynomial Reduction"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("integer-to-rational-solvability"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Diophantine/IntegerToRational.solvability"),
                H("The finite joint-assignment reduction"),
                StatementSource.FromAuthor(Presentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Fix an integer polynomial P in one input coordinate and m witness "
                        + "coordinates that existentially defines the integers inside the rationals. "
                        + "For an arbitrary input polynomial f in n integer variables, the compiler "
                        + "uses n disjoint blocks of m+1 rational coordinates. The first coordinate "
                        + "of each block is the corresponding input variable; the remaining m "
                        + "coordinates are that variable's defining witnesses. DefinesIntegers P "
                        + "means: for every rational q, there exist m rational witnesses w with "
                        + "P(q,w)=0 if and only if there exists an integer z whose rational cast "
                        + "equals q. No integrality condition is imposed on the witnesses.")),
                    Paragraph(Text(
                        "The output is one integer-coefficient polynomial: the square of f on the "
                        + "first coordinates plus the sum of the squares of the n translated copies "
                        + "of P. Every equation is evaluated under one joint assignment. A zero sum "
                        + "of rational squares forces every summand to vanish, giving soundness; an "
                        + "integer zero of f and one defining witness block per coordinate give "
                        + "completeness. The proof includes n=0, constant and zero inputs, signs and "
                        + "all finite dimensions.")),
                    Paragraph(Text(
                        "This is conditional. It neither constructs the defining polynomial P nor "
                        + "proves integer Hilbert-tenth undecidability. The semantic compiler is "
                        + "formalized here. The companion effective theorem fixes a total raw Nat code, "
                        + "proves code completeness, and supplies a primitive-recursive compiler whose "
                        + "decoded output is this same semantic compiler. The implication is "
                        + "classical; the finite code construction below is an explicit realization. "
                        + "The entire integrality clause of ZInQ.FrozenTarget is an admissible "
                        + "premise; its degree and coefficient bounds are not needed."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-to-rational-primitive-recursion"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Diophantine/IntegerToRational.compileCodeNat_primrec"),
                H("Primitive recursiveness at the fixed raw coding"),
                StatementSource.FromAuthor(F.Disp(Call("Primrec", F.Id("K")))),
                AssessedProvenance.FromRepo(),
                Blocks(Paragraph(Text(
                    "K is the uncurried map compileCodeNat on the right-associated natural tuple "
                    + "(n,m,p,f). It returns (n*(m+1),k), where k encodes the compiled polynomial. "
                    + "Both dimensions vary uniformly. The proof composes Mathlib's primitive-recursive "
                    + "natural arithmetic, bounded comparison, canonical decoding and encoding, list "
                    + "map, concatenation, flatMap and range operations. The claim uses Mathlib.Primrec, "
                    + "with its natural-number encoding semantics."))),
                DescribeRole.Theorem),
            Describe.Lean(
                DescribeId.Create("integer-to-rational-effective-compiler"),
                DeclarationHandle.Create(
                    "D5/S0/Computability/Diophantine/IntegerToRational.effective_compiler"),
                H("The total primitive-recursive code compiler"),
                StatementSource.FromAuthor(EffectivePresentation()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Polynomial codes are finite lists of signed-coefficient monomials. "
                        + "A coefficient is a difference of naturals and a variable word uses "
                        + "natural indices; an index outside the declared finite dimension is "
                        + "interpreted as zero. A term ((a,b),[k,...]) decodes to the constant "
                        + "a-b times the product of those variables. Repeated indices give powers; "
                        + "the empty product is one and the empty term list is zero. Raw Nat codes "
                        + "use the pinned Mathlib Encodable product/list numbering; a failed decode "
                        + "returns the empty code. Every signed coefficient and every finite "
                        + "MvPolynomial, including dimension zero, is represented.")),
                    Paragraph(Text(
                        "Coordinate j of block i has index j+(m+1)*i. Input variables are renamed "
                        + "to (m+1)*i, and each copy of P is renamed to its own block. Invalid source "
                        + "indices are sent to the output dimension, so they still denote zero. "
                        + "Code multiplication distributes terms and concatenates variable words; "
                        + "the compiler squares the renamed input and adds the n squared row codes. "
                        + "Polynomial induction proves completeness. decode_compileCode proves "
                        + "that this code operation decodes to the semantic sum of squares.")),
                    Paragraph(Text(
                        "The compiler takes both dimensions and both raw codes as inputs. Its "
                        + "natural/list operations are proved primitive recursive, every finite "
                        + "MvPolynomial has a code, and the decoded result has the same rational "
                        + "solvability equivalence as the semantic joint-assignment reduction. "
                        + "In the formula, K denotes the uncurried map compileCodeNat on the "
                        + "right-associated tuple (n,m,p,f), returning the output dimension and "
                        + "raw polynomial code. D(n,k) denotes decodePolynomial n (decodeCode k), "
                        + "and snd selects the output code. The theorem compileCodeNat_primrec "
                        + "proves the stronger primitive-recursive property; effective_compiler "
                        + "combines its computability consequence with completeness and solvability."))),
                DescribeRole.Theorem))));

    private static Formula A(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.ForAll, FormulaIdentifier.Create(name), domain, body);

    private static Formula E(string name, Formula domain, Formula body) =>
        new Formula.Bind(FormulaQuantifier.Exists, FormulaIdentifier.Create(name), domain, body);

    private static Formula Presentation()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var p = F.Id("P");
        var f = F.Id("f");
        var lhs = E("x", Call("FinRatVec", Call("mul", n, Call("succ", m))),
            Call("evalCompiled", p, f, F.Id("x"), F.Id("zero")));
        var rhs = E("z", Call("FinIntVec", n),
            Call("evalInput", f, F.Id("z"), F.Id("zero")));
        var body = F.Seq(
            Call("DefinesIntegers", p), F.Sp, Rightarrow, F.Sp, F.Open,
            F.Open, lhs, F.Close, F.Sp, Iff, F.Sp, F.Open, rhs, F.Close, F.Close);
        return F.Disp(A("n", F.Id("N"), A("m", F.Id("N"),
            A("P", Call("IntegerPolynomial", Call("succ", m)),
                A("f", Call("IntegerPolynomial", n), body)))));
    }

    private static Formula EffectivePresentation()
    {
        var n = F.Id("n");
        var m = F.Id("m");
        var p = F.Id("p");
        var f = F.Id("f");
        var dimension = Call("mul", n, Call("succ", m));
        var completeness = A("n", F.Id("N"),
            A("f", Call("IntegerPolynomial", n), E("k", F.Id("N"),
                F.Seq(Call("D", n, F.Id("k")), F.Sp, Eq, F.Sp, f))));
        var lhs = E("x", Call("FinRatVec", dimension),
            F.Seq(Call("evalRat", Call("D", dimension,
                    Call("snd", Call("K", n, m, p, f))), F.Id("x")),
                F.Sp, Eq, F.Sp, D(0)));
        var rhs = E("z", Call("FinIntVec", n),
            F.Seq(Call("evalInt", Call("D", n, f), F.Id("z")),
                F.Sp, Eq, F.Sp, D(0)));
        var preservation = A("n", F.Id("N"), A("m", F.Id("N"),
            A("p", F.Id("N"), A("f", F.Id("N"),
                F.Seq(Call("DefinesIntegers", Call("D", Call("succ", m), p)),
                    F.Sp, Rightarrow, F.Sp, F.Open, F.Open, lhs, F.Close,
                    F.Sp, Iff, F.Sp, F.Open, rhs, F.Close, F.Close)))));
        return F.Disp(F.Seq(Call("Computable", F.Id("K")), F.Sp, Land, F.Sp,
            F.Open, completeness, F.Close, F.Sp, Land, F.Sp,
            F.Open, preservation, F.Close));
    }
}
