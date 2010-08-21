require 'rubygems'
require 'bundler'
Bundler.setup

$: << File.dirname(__FILE__)
require 'example/example'
require 'example/sinatra'
