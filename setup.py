from setuptools import setup, find_packages
from setuptools import Command
from setuptools import Extension
from Cython.Build import cythonize
from sage.all import *


setup(
    name='Disproving',
    version='1.0',
    packages=find_packages(),
    description='Disproving ideal membership via sat solvers',
    author='Peter Krug',
    author_email='p98krug.pk@gmx.de',
    install_requires=[
        'pysat',
        'operator_gb @ git+https://github.com/ClemensHofstadler/operator_gb.git@main#egg=operator_gb'
    ]
)
