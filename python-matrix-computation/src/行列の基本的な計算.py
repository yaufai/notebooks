# -*- coding: utf-8 -*-
# ---
# jupyter:
#   jupytext:
#     text_representation:
#       extension: .py
#       format_name: light
#       format_version: '1.5'
#       jupytext_version: 1.13.5
#   kernelspec:
#     display_name: Python 3
#     language: python
#     name: python3
# ---

import numpy as np

# # 行列の定義
#
# 二重リストを`np.matrix`に与える

A = np.matrix([
    [3., 1., 2.],
    [2., 3., 1.]
])

B = np.matrix([
    [1 + 2j, 1 - 1j],
    [3j    , 2 + 1j]
])

A

B

# ## 単位行列の定義

I = np.identity(4)
I

# # 定数倍
#
# 左から定数をかける

2*A

# # 行列同士の加減

A + A

A - A

# # 行列の積

np.matmul(B, B)

# # 行列のHadamard積

np.multiply(A, A)

np.multiply(B, B)

# # 転置・Helmite転置
#
# - `np.transpose(...)`: 転置
# - `np.conjugate(...)`: Helmite転置

At = np.transpose(A)

At

Bt = np.conjugate(B)

Bt

# # 逆行列
#
# `linalg`(LINear ALGebra)ライブラリを使う

Binv = np.linalg.inv(B)

Binv

np.matmul(B, Binv)

# 正方行列ではなければ失敗する

np.linalg.inv(A)

# # 行列式をもとめる

np.linalg.det(B)








