using static StrataLint.Scribe.DefinitionDsl;
using static StrataLint.Scribe.FormulaDsl;
using F = StrataLint.Scribe.FormulaDsl;

namespace StrataLint.Scribe.Blueprint.D5.S3.Arith.Coding;

internal sealed class ResidueCodeDynamicRangeDocument : IScribeDocumentDefinition
{
    public DocumentDefinition Create() => DocumentDefinition.Create(ScribeNode.Create(
        "For an ordered coprime residue system, the protected message range is determined "
            + "exactly by the product of its smallest moduli.",
        H("Dynamic Range and Minimum Distance of Residue Codes"),
        Blocks(
            Describe.Lean(
                DescribeId.Create("strictly-increasing-finite-indices-dominate-their-ranks"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/ResidueCodeDynamicRange.fin_index_le_strict_mono"),
                H("A strictly increasing finite index selection dominates its ranks"),
                StatementSource.FromAuthor(FinIndexFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "A strictly increasing map from the first k indices into the first n "
                            + "indices cannot send any rank i below i. In other words, the i-th "
                            + "selected coordinate is always at least the i-th coordinate of the "
                            + "initial segment.")),
                    Paragraph(Text(
                        "The argument proceeds by rank. Rank zero has the required lower bound "
                            + "automatically. At the next rank, strict increase places its image "
                            + "strictly above the preceding image; the induction bound on that "
                            + "preceding image then forces the new image to be at least the new rank."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("selected-residue-agreement-is-product-divisibility"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/ResidueCodeDynamicRange.agree_on_iff_prod_dvd"),
                H("Selected residue agreement is equivalent to product divisibility"),
                StatementSource.FromAuthor(AgreementFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Choose k coordinates of an n-coordinate residue word and suppose the "
                            + "moduli at those coordinates are pairwise coprime. For messages x and "
                            + "y with x at most y, their residues agree at every selected coordinate "
                            + "exactly when the product of all selected moduli divides y minus x.")),
                    Paragraph(Text(
                        "Agreement modulo each selected modulus makes every factor divide the "
                            + "message difference. Pairwise coprimality combines these divisibilities "
                            + "into divisibility by the full product. Conversely, each selected "
                            + "modulus divides that product, so product divisibility recovers every "
                            + "individual congruence and hence every selected residue equality."))),
                DescribeRole.Lemma),
            Describe.Lean(
                DescribeId.Create("maximum-dynamic-range-is-equivalent-to-minimum-distance"),
                DeclarationHandle.Create(
                    "D5/S3/Arith/Coding/ResidueCodeDynamicRange."
                        + "maximum_dynamic_range_iff_min_distance"),
                H("Maximum dynamic range is equivalent to the minimum-distance bound"),
                StatementSource.FromAuthor(DynamicRangeFormula()),
                AssessedProvenance.FromRepo(),
                Blocks(
                    Paragraph(Text(
                        "Let the first n moduli be positive, nondecreasing, and pairwise coprime, "
                            + "and let d lie between one and n. The residue code on messages below K "
                            + "has Hamming distance at least d precisely when K is no larger than the "
                            + "product of the first n - d + 1 moduli.")),
                    Paragraph(Text(
                        "If K exceeds that prefix product, the messages zero and the prefix product "
                            + "both lie in the range and agree on those first coordinates, leaving "
                            + "fewer than d disagreements. This supplies the concrete obstruction to "
                            + "any larger dynamic range.")),
                    Paragraph(Text(
                        "For the converse, a pair at distance below d agrees on at least n - d + 1 "
                            + "coordinates. Coprimality makes the product of their selected moduli "
                            + "divide the positive message difference, while monotonicity makes that "
                            + "selected product at least the initial prefix product. The assumed "
                            + "range bound then puts K below the difference, contradicting that both "
                            + "messages lie below K."))),
                DescribeRole.Theorem))));

    private static Formula FinIndexFormula()
    {
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula f = F.Id("f");
        Formula i = F.Id("i");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));

        return Disp(Seq(
            Forall, Sp, k, Comma, Sp, n, Sp, InMacro, Sp, naturals, Comma, Sp,
            Forall, Sp, f, Colon, Sp, Call("Fin", k), Sp, To, Sp, Call("Fin", n),
            Comma, Sp, Call("StrictMono", f), Sp, Rightarrow, Sp,
            Forall, Sp, i, Sp, InMacro, Sp, Call("Fin", k), Comma, Sp,
            i, Sp, Leq, Sp, Call("f", i), Dot));
    }

    private static Formula AgreementFormula()
    {
        Formula k = F.Id("k");
        Formula n = F.Id("n");
        Formula m = F.Id("m");
        Formula f = F.Id("f");
        Formula x = F.Id("x");
        Formula y = F.Id("y");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula selectedI = Call("f", i);
        Formula selectedJ = Call("f", j);
        Formula modulusI = Call("m", selectedI);
        Formula modulusJ = Call("m", selectedJ);
        Formula selectedProduct = Seq(
            Prod, Underscore, Grp(i, Sp, InMacro, Sp, Call("Fin", k)), Sp,
            Call("m", Call("f", i)));

        return Disp(Seq(
            Forall, Sp, k, Comma, Sp, n, Comma, Sp, x, Comma, Sp, y,
            Sp, InMacro, Sp, naturals, Comma, Sp,
            Forall, Sp, m, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            Forall, Sp, f, Colon, Sp, Call("Fin", k), Sp, To, Sp, Call("Fin", n),
            Comma, Sp, x, Sp, Leq, Sp, y, Comma, Sp,
            Open, Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, Call("Fin", k),
            Comma, Sp, i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Gcd, Open, modulusI, Comma, Sp, modulusJ, Close, Sp, Eq, Sp, D(1), Close,
            Sp, Rightarrow, Sp, Open,
            Open, Forall, Sp, i, Sp, InMacro, Sp, Call("Fin", k), Comma, Sp,
            Call("residueWord", m, n, x, selectedI), Sp, Eq, Sp,
            Call("residueWord", m, n, y, selectedI), Close,
            Sp, Iff, Sp, selectedProduct, Sp, Mid, Sp, y, Sp, Minus, Sp, x,
            Close, Dot));
    }

    private static Formula DynamicRangeFormula()
    {
        Formula m = F.Id("m");
        Formula n = F.Id("n");
        Formula d = F.Id("d");
        Formula range = F.Id("K");
        Formula i = F.Id("i");
        Formula j = F.Id("j");
        Formula naturals = Seq(Mathbb, Grp(F.Id("N")));
        Formula modulusI = Call("m", i);
        Formula modulusJ = Call("m", j);
        Formula prefixLength = Seq(n, Sp, Minus, Sp, d, Sp, Plus, Sp, D(1));

        return Disp(Seq(
            Forall, Sp, m, Colon, Sp, naturals, Sp, To, Sp, naturals, Comma, Sp,
            Forall, Sp, n, Comma, Sp, d, Comma, Sp, range,
            Sp, InMacro, Sp, naturals, Comma, Sp,
            D(1), Sp, Leq, Sp, d, Sp, Leq, Sp, n, Comma, Sp,
            Open, Forall, Sp, i, Comma, Sp, j, Sp, InMacro, Sp, naturals, Comma, Sp,
            i, Sp, Leq, Sp, j, Sp, Land, Sp, j, Sp, Lt, Sp, n,
            Sp, Rightarrow, Sp, modulusI, Sp, Leq, Sp, modulusJ, Close,
            Comma, Sp, Open, Forall, Sp, i, Sp, InMacro, Sp, naturals, Comma, Sp,
            i, Sp, Lt, Sp, n, Sp, Rightarrow, Sp, D(0), Sp, Lt, Sp, modulusI, Close,
            Comma, Sp, Open, Forall, Sp, i, Comma, Sp, j,
            Sp, InMacro, Sp, naturals, Comma, Sp,
            i, Sp, Lt, Sp, n, Sp, Land, Sp, j, Sp, Lt, Sp, n, Sp, Land, Sp,
            i, Sp, Neq, Sp, j, Sp, Rightarrow, Sp,
            Gcd, Open, modulusI, Comma, Sp, modulusJ, Close, Sp, Eq, Sp, D(1), Close,
            Comma, Sp, Call("MinDistanceAtLeast", m, n, range, d),
            Sp, Iff, Sp, range, Sp, Leq, Sp,
            Call("prefixProduct", m, prefixLength), Dot));
    }
}
