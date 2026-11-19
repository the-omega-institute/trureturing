using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.QuadraticForms;

internal sealed class LieRadicalTransferDocument : IScribeDocumentDefinition
{
    private const string Prefix = "D5/S3/QuadraticForms/LieRadicalTransfer.";
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "Solvable extensions and actual radical quotients.", H("Lie radical transfer"),
        Blocks(
            Entry("nilpotent_of_triple_bracket_zero", "A uniform two-step nilpotence bound",
                LContext(Imp(All(X("x"), X("L"), All(X("y"), X("L"), All(X("z"), X("L"),
                    Eq(Call("lie", X("x"), Call("lie", X("y"), X("z"))), D(0))))),
                    Call("LieRing.IsNilpotent", X("L")))),
                "If every nested triple bracket vanishes, the actual lower central series vanishes at step two. This includes the zero algebra. The canonical proof is shared with the pointwise-stabilizer kernel and the full derivation-kernel construction.", DescribeRole.Theorem),
            Entry("solvable_comap", "Solvable inverse images",
                PairContext(All(X("f"), Hom(X("L"), X("M")), Instance(Solvable(Ker),
                    All(X("I"), Call("LieIdeal", X("k"), X("M")), Instance(Solvable(X("I")),
                        Solvable(Call("LieIdeal.comap", X("I"), X("f")))))))),
                "For any Lie map with solvable kernel, the inverse image of a solvable ideal is solvable. Restrict the map to that inverse image and embed its kernel into the original solvable kernel. Surjectivity and finite dimensionality are not required.", DescribeRole.Theorem),
            Entry("injective_on_simple_ideal", "Simple ideals survive solvable kernels",
                PairContext(All(X("f"), Hom(X("L"), X("M")), Instance(Solvable(Ker),
                    All(X("I"), Call("LieIdeal", X("k"), X("L")), Instance(Call("LieAlgebra.IsSimple", X("k"), X("I")),
                        Call("Function.Injective", Call("LieHom.comp", X("f"), Call("LieIdeal.incl", X("I"))))))))),
                "The restriction of any map with solvable kernel to an actual nonabelian simple ideal is injective. The restriction kernel embeds into the original solvable kernel; the simple ideal has trivial radical, so that restriction kernel vanishes.", DescribeRole.Theorem),
            Entry("simpleIdealEquiv_of_surjection", "A nonzero simple factor projection",
                SimpleProjectionFormula(),
                "A surjective map onto a nonabelian simple Lie algebra restricts to a Lie equivalence on any nonabelian simple ideal with nonzero image. Surjectivity ensures its image is an actual target ideal. Its kernel vanishes by source simplicity and nonzero image, and its image is the full target by target simplicity.", DescribeRole.Definition),
            Entry("isSimple_of_equiv", "Simplicity under an actual equivalence",
                PairContext(Instance(Call("LieAlgebra.IsSimple", X("k"), X("L")),
                    All(X("e"), Call("LieEquiv", X("k"), X("L"), X("M")), Call("LieAlgebra.IsSimple", X("k"), X("M"))))),
                "An actual Lie equivalence transports the ideal dichotomy and nonabelian condition. The G2 exclusion uses this to transport simplicity from the actual hypothetical simple ideal to mathlib's actual Serre object.", DescribeRole.Theorem),
            Entry("solvable_of_solvable_kernel", "Solvable extensions",
                PairContext(All(X("f"), Hom(X("L"), X("M")),
                    Instance(Solvable(Ker), Instance(Solvable(X("M")), Solvable(X("L")))))),
                "For any Lie homomorphism over a field, a solvable kernel and a solvable codomain imply a solvable domain. The proof bounds the derived series of the domain first by the kernel and then by its own derived series. Surjectivity is not assumed.", DescribeRole.Theorem),
            Entry("kernel_eq_radical", "Identification of the actual radical",
                QuotientContext(Eq(Ker, Rad)),
                "For a Noetherian Lie algebra over a field, a surjective Lie map with solvable kernel and radical-free target has kernel equal to the actual solvable radical. The radical has solvable image under the surjection; that image must vanish. The reverse containment uses solvability of the kernel.", DescribeRole.Theorem),
            Entry("quotientEquiv_of_solvable_kernel", "An actual quotient equivalence",
                QuotientContext(Seq(X("quotientEquiv"), Sp, Colon, Sp,
                    Call("LieEquiv", X("k"), Call("Quotient", X("L"), Rad), X("M")))),
                "Under the same field, Lie algebra, Noetherian, surjectivity, solvable-kernel and trivial-target-radical hypotheses, the first isomorphism theorem gives an actual Lie equivalence from L modulo its actual radical to M. This conditional transfer lemma does not construct the required map for an evolution algebra.", DescribeRole.Definition),
            Entry("hasTrivialRadical_of_separating_surjections", "Separating radical-free quotients",
                SeparatingFormula(),
                "A family of surjective Lie maps to radical-free targets makes L radical-free when their kernels have zero intersection, stated by the exact separating law on each x. The index type can be infinite or empty; no finite dimensionality is required. Every abelian ideal has zero image in every target and therefore vanishes. These are classical Lie facts supporting the Ma-then-Zhang credited KMV application, not a priority claim or a completed evolution-algebra classification.", DescribeRole.Theorem))));
    private static Formula SimpleProjectionFormula()
    {
        var i = X("I"); var f = X("f");
        Formula body = Call("LieEquiv", X("k"), i, X("M"));
        body = Imp(Seq(Exists, Sp, X("x"), Sp, Colon, Sp, i, Comma, Sp,
            new Formula.Relation(App(f, Call("Subtype.val", X("x"))), FormulaRelationOperator.NotEqual, D(0))), body);
        body = Instance(Call("LieAlgebra.IsSimple", X("k"), i), body);
        body = All(i, Call("LieIdeal", X("k"), X("L")), body);
        body = Imp(Call("Function.Surjective", f), body);
        return PairContext(Instance(Call("LieAlgebra.IsSimple", X("k"), X("M")), All(f, Hom(X("L"), X("M")), body)));
    }
    private static Formula SeparatingFormula()
    {
        var index = X("aType");
        var a = X("a");
        var h = App(X("H"), a);
        Formula body = RadicalFree(X("L"));
        body = Imp(All(X("x"), X("L"),
            Imp(All(a, index, Eq(App(X("f"), a, X("x")), D(0))), Eq(X("x"), D(0)))), body);
        body = Imp(All(a, index, Call("Function.Surjective", App(X("f"), a))), body);
        body = All(X("f"), All(a, index, Hom(X("L"), h)), body);
        body = Instance(All(a, index, RadicalFree(h)), body);
        body = Instance(All(a, index, Call("LieAlgebra", X("k"), h)), body);
        body = Instance(All(a, index, Call("LieRing", h)), body);
        return LContext(All(index, Type, All(X("H"), new Formula.TypeArrow(index, Type), body)));
    }
    private static DocumentBlock.Describe Entry(string name, string title, Formula formula, string text, DescribeRole role) =>
        Describe.Lean(DescribeId.Create(name.Replace('_','-').ToLowerInvariant()),
            DeclarationHandle.Create(Prefix + name), H(title), StatementSource.FromAuthor(Disp(formula)),
            AssessedProvenance.FromRepo(), Blocks(Paragraph(Text(text))), role);
    private static Formula X(string s) => F.Id(s);
    private static Formula Type => Call("Type");
    private static Formula Qualified(string s) => Seq(s.Split('.').SelectMany((part, i) =>
        i == 0 ? new Formula[] { Seq(Operatorname, Grp(X(part))) } :
            new Formula[] { Dot, Seq(Operatorname, Grp(X(part))) }).ToArray());
    private static Formula Call(string s, params Formula[] xs) => new Formula.Apply(Qualified(s), [.. xs]);
    private static Formula App(Formula f, params Formula[] xs) => new Formula.Apply(f, [.. xs]);
    private static Formula All(Formula x, Formula t, Formula b) => Seq(Forall, Sp, Open, x, Sp, Colon, Sp, t, Close, Comma, Sp, Open, b, Close);
    private static Formula Instance(Formula t, Formula b) => Seq(OpenBracket, t, CloseBracket, Sp, b);
    private static Formula Par(Formula f) => Seq(Open, f, Close);
    private static Formula Imp(Formula a, Formula b) => new Formula.Logic(Par(a), FormulaLogicOperator.Implies, Par(b));
    private static Formula Eq(Formula a, Formula b) => new Formula.Relation(a, FormulaRelationOperator.Equal, b);
    private static Formula Hom(Formula l, Formula m) => Call("LieHom", X("k"), l, m);
    private static Formula Solvable(Formula l) => Call("LieAlgebra.IsSolvable", l);
    private static Formula RadicalFree(Formula l) => Call("LieAlgebra.HasTrivialRadical", X("k"), l);
    private static Formula Rad => Call("LieAlgebra.radical", X("k"), X("L"));
    private static Formula Ker => Call("LieHom.ker", X("f"));
    private static Formula LieContext(Formula l, Formula b) => All(l, Type,
        Instance(Call("LieRing", l), Instance(Call("LieAlgebra", X("k"), l), b)));
    private static Formula LContext(Formula b) => All(X("k"), Type,
        Instance(Call("Field", X("k")), LieContext(X("L"), b)));
    private static Formula PairContext(Formula b) => LContext(LieContext(X("M"), b));
    private static Formula QuotientContext(Formula b) => PairContext(
        Instance(Call("IsNoetherian", X("k"), X("L")), All(X("f"), Hom(X("L"), X("M")),
        Imp(Call("Function.Surjective", X("f")), Instance(Solvable(Ker), Instance(RadicalFree(X("M")), b))))));
}
