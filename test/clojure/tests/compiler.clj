(ns clojure.tests.compiler
  (:refer-clojure :exclude [*source* *source-path* *compile-files* *compile-path*
                            munge macroexpand-1 macroexpand])
  (:use [clojure.compiler])
  (:use [clojure.test]))


(deftest test-literal-expressions
  (is (= #clojure.compiler.ConstantExpr{:v #{1 2 3 4}, :id -1}
         (analyze :expression #{1 2 3 4})))
  (is (= #clojure.compiler.ConstantExpr{:v {1 2 3 4}, :id -1}
         (analyze :expression {1 2 3 4})))
  (is (= #clojure.compiler.ConstantExpr{:v [1 2 3 4], :id -1}
         (analyze :expression [1 2 3 4])))
  (is (= #clojure.compiler.NumberExpr{:n 123, :id -1}
         (analyze :expression 123)))
  (is (= #clojure.compiler.StringExpr{:str "abcd"}
         (analyze :expression "abcd"))))

(deftest test-if-expression
  (is (= 1 (evaluate (analyze :expression '(if true 1 2)))))
  (is (= 2 (evaluate (analyze :expression '(if false 1 2))))))

(deftest test-macro-expansion
  (is (= '(if 1 (do 2 3)) (macroexpand-1 '(when 1 2 3)))))