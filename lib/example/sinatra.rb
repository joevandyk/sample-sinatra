require 'sinatra'
require 'json'
class SinatraApp < Sinatra::Base

  get '/' do
    content_type 'json'
    {:result => Example.get_something, :params => params}.to_json
  end

end
